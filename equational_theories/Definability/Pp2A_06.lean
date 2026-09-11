import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_pxx_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq11 (M.op X0 (M.op X1 X1)) X1
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
  have eq100 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq45
    | (have j0 := eq45 (M.op x y)
       grind)
    | exact resolve eq45 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
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
  have eq188 : ∀ X2 X3 : G, (M.op x y) = (M.op x (M.op X2 (M.op X3 (M.op x y)))) := by
    intro X2 X3
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op (σ x) (σ y))))) := by
    intro X2 X3
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 (k X0 X1))) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq611 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X1) (M.op X2 (M.op X3 X1))) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq630 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
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
  have eq635 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq640 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq630
       grind)
    | exact superpose eq630 eq40
    | exact resolve eq40 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq643 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq642
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq642
    | exact resolve eq642 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq645 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq643
    | exact resolve eq643 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq645 eq635
    | exact resolve eq635 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq662 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq655
       have r₂ := eq27
       grind)
    | exact resolve eq655 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq667 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq662 eq176
    | exact resolve eq176 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq668 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq662 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq662 eq181
    | exact resolve eq181 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq662 eq13
    | exact resolve eq13 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (σ y))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq662 eq16
    | exact resolve eq16 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq668
       have r₂ := eq670
       grind)
    | exact resolve eq668 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq670
  have eq679 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq178 eq177
    | exact resolve eq177 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq179 eq177
    | exact resolve eq177 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq720 : (τ (σ y)) = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq673 eq98
    | exact resolve eq98 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq673
  have eq726 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq720
    | exact resolve eq720 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq731 : x ≠ y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq640 x
       have i₂ := eq726
       grind)
    | exact superpose eq726 eq640
    | (have j0 := eq640 x
       grind)
    | exact resolve eq640 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq667
    | (have j0 := eq667 (σ x)
       grind)
    | exact resolve eq667 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq752 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq739 eq192
    | exact resolve eq192 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq1182 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq610 x x X0 X1
       have i₂ := eq726
       grind)
    | exact superpose eq726 eq610
    | (have j0 := eq610 x x x x
       grind)
    | exact resolve eq610 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1196 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X3 X0)) = (M.op X1 (k X0 X2)) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X1 (k X0 X2) X3 (M.op X0 x)
       have i₂ := eq610 X0 X2 x X1
       grind)
    | exact superpose eq610 eq177
    | (have j1 := eq610 X0 X2 X2 X3
       grind)
    | exact resolve eq177 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1210 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1182 X0 x
       have i₂ := eq698 (M.op x X0) x
       grind)
    | (have i₁ := eq1182 X0 x
       have i₂ := eq698 (M.op x X0) x
       grind)
    | exact superpose eq698 eq1182
    | (have j0 := eq1182 X0 x
       grind)
    | exact resolve eq1182 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1212 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq28 eq1210
    | (have j0 := eq1210 X0
       have j1 := eq28 x x
       grind)
    | exact resolve eq1210 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1213 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = y ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq726 eq1212
    | (have j0 := eq1212 X0
       grind)
    | exact resolve eq1212 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1216 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq611 x x X0 X1
       have i₂ := eq726
       grind)
    | exact superpose eq726 eq611
    | (have j0 := eq611 x x x x
       grind)
    | exact resolve eq611 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1314 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ x = (M.op x x) ∨ y = (k x x) := by
    intro X0 X1
    first
    | exact superpose eq28 eq1216
    | (have j0 := eq1216 X0 X1
       have j1 := eq28 x x
       grind)
    | exact resolve eq1216 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1320 : ∀ X0 : G, x = (M.op y (M.op X0 (k x x))) ∨ x = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq1196 eq1314
    | (have j1 := eq1196 x x x x
       grind)
    | exact resolve eq1314 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq1321 : ∀ X0 : G, x = (M.op y (M.op X0 (k x x))) ∨ x = y ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq726 eq1320
    | (have j0 := eq1320 X0
       grind)
    | exact resolve eq1320 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq1320
  have eq1427 : ∀ X1 : G, y = (M.op x (M.op X1 (M.op x y))) ∨ x = y ∨ y = (k x x) := by
    intro X1
    first
    | (have i₁ := eq178 (M.op x (k x x)) X1
       have i₂ := eq1321 x
       grind)
    | exact superpose eq1321 eq178
    | exact resolve eq178 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1445 : x = (M.op y (M.op x y)) ∨ x = y ∨ y = (k x x) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq1427 eq1213
    | exact resolve eq1213 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213 eq1427
  have eq1458 : y = (k x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by grind
  clear eq1445
  have eq1467 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq611 x x X0 X1
       have i₂ := eq1458
       grind)
    | exact superpose eq1458 eq611
    | (have j0 := eq611 x x x x
       grind)
    | exact resolve eq611 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1470 : ∀ X0 : G, x = (M.op y (M.op X0 (k x x))) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1196 eq1467
    | (have j1 := eq1196 x x x x
       grind)
    | exact resolve eq1467 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq1473 : ∀ X0 : G, x = (M.op y (M.op X0 y)) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1458 eq1470
    | exact resolve eq1470 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458 eq1470
  have eq1476 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1473 x
       have i₂ := eq698 y x
       grind)
    | (have i₁ := eq1473 x
       have i₂ := eq698 y x
       grind)
    | exact superpose eq698 eq1473
    | (have j0 := eq1473 x
       grind)
    | exact resolve eq1473 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1477 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq1476
  have eq1496 : ∀ X0 : G, y = (M.op x (M.op X0 (M.op x y))) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1477 eq178
    | exact resolve eq178 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1515 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq1477 eq1496
    | exact resolve eq1496 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477 eq1496
  have eq1531 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq1515
  have eq1538 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1531
       have r₂ := eq731
       grind)
    | exact resolve eq1531 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq1531
  have eq1543 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq175 X0 x
       have i₂ := eq1538
       grind)
    | exact superpose eq1538 eq175
    | exact resolve eq175 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1547 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 X1 x
       have i₂ := eq1538
       grind)
    | exact superpose eq1538 eq16
    | exact resolve eq16 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1548 : y = (k x x) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq1538
       grind)
    | exact superpose eq1538 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1553 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq1538
  have eq1556 : y = (k x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1548
       have r₂ := eq1553
       grind)
    | exact resolve eq1548 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548 eq1553
  have eq1557 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1547 X0 x
       have i₂ := eq698 (M.op x X0) x
       grind)
    | (have i₁ := eq1547 X0 x
       have i₂ := eq698 (M.op x X0) x
       grind)
    | exact superpose eq698 eq1547
    | (have j0 := eq1547 X0 x
       grind)
    | exact resolve eq1547 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547
  have eq1559 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1543 x
       have i₂ := eq698 sF0 x
       grind)
    | (have i₁ := eq1543 x
       have i₂ := eq698 sF0 x
       grind)
    | exact superpose eq698 eq1543
    | (have j0 := eq1543 x
       grind)
    | exact resolve eq1543 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1564 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1556
       grind)
    | exact superpose eq1556 eq40
    | exact resolve eq40 eq1556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556
  have eq1573 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1564
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1564
    | exact resolve eq1564 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1576 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1573
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1573
    | exact resolve eq1573 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq1586 : x ≠ (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1559 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq1559
       grind)
    | exact resolve eq13 eq1559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1589 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1559 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq1559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559
  have eq1595 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1586
       have r₂ := eq1589
       grind)
    | exact resolve eq1586 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586 eq1589
  have eq1622 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (M.op X0 (M.op X1 (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq1576 eq611
    | (have j0 := eq611 (σ x) (σ x) x x
       grind)
    | exact resolve eq611 eq1576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1625 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (k (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1196 eq1622
    | (have j1 := eq1196 (σ x) x (σ x) x
       grind)
    | exact resolve eq1622 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622
  have eq1629 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1576 eq1625
    | exact resolve eq1625 eq1576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576 eq1625
  have eq1632 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq699 eq1629
    | (have j0 := eq1629 (σ x)
       grind)
    | exact resolve eq1629 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq1629
  have eq1634 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1595 eq42
    | exact resolve eq42 eq1595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595
  have eq1638 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1634
    | exact resolve eq1634 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634
  have eq1640 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1638
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1638
    | exact resolve eq1638 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638
  have eq1645 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1640 eq640
    | (have j0 := eq640 (σ (M.op x y))
       grind)
    | exact resolve eq640 eq1640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq1646 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq1640 eq611
    | (have j0 := eq611 (σ (M.op x y)) (σ (M.op x y)) x x
       grind)
    | exact resolve eq611 eq1640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1648 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1196 eq1646
    | (have j1 := eq1196 (σ (M.op x y)) x (σ (M.op x y)) x
       grind)
    | exact resolve eq1646 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq1652 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1640 eq1648
    | exact resolve eq1648 eq1640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq2560 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1632 eq192
    | exact resolve eq192 eq1632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq1632
  have eq3243 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq662 eq679
    | exact resolve eq679 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq3296 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq645 eq3243
    | exact resolve eq3243 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3243
  have eq3367 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3296 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3296
       grind)
    | exact resolve eq13 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296
  have eq3379 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq3367
  have eq3391 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq3379
    | exact resolve eq3379 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3379
  have eq3396 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq645 eq3391
    | exact resolve eq3391 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3391
  have eq3397 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq3396
       have r₂ := eq27
       grind)
    | exact resolve eq3396 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3396
  have eq3401 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3397 eq669
    | exact resolve eq669 eq3397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq3403 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3397 eq671
    | exact resolve eq671 eq3397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq3414 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3397 eq181
    | exact resolve eq181 eq3397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq3397
  have eq3420 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ (M.op x y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq3403 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3403
  have eq3421 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq3401
  have eq3458 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3421 eq28
    | (have j0 := eq28 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq28 eq3421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421
  have eq3610 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq662 eq3420
    | exact resolve eq3420 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq3420
  have eq3634 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq3610
  have eq3643 : (σ (M.op x y)) ≠ (σ x) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3634 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq13 eq3634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3634
  have eq5202 : (τ (σ y)) = (k x (M.op x y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3458 eq100
    | exact resolve eq100 eq3458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq3458
  have eq5215 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k x (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq5202
    | exact resolve eq5202 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq5202
  have eq5324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (k x (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5215 eq3414
    | exact resolve eq3414 eq5215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3414 eq5215
  have eq5350 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (k x (M.op x y)) := by grind
  clear eq5324
  have eq5360 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (k x (M.op x y)) := by
    first
    | exact superpose eq26 eq5350
    | exact resolve eq5350 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5350
  have eq5365 : y = (k x (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq5360
       have r₂ := eq27
       grind)
    | exact resolve eq5360 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5360
  have eq5372 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq5365 eq610
    | (have j0 := eq610 x (M.op x y) x x
       grind)
    | exact resolve eq610 eq5365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610 eq5365
  have eq5373 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq5372 X0 x
       have i₂ := eq698 (M.op x X0) x
       grind)
    | (have i₁ := eq5372 X0 x
       have i₂ := eq698 (M.op x X0) x
       grind)
    | exact superpose eq698 eq5372
    | (have j0 := eq5372 X0 x
       grind)
    | exact resolve eq5372 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq5372
  have eq5378 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1557 eq5373
    | (have j0 := eq5373 X0
       have j1 := eq1557 X0
       grind)
    | exact resolve eq5373 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557 eq5373
  have eq5491 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq188 eq5378
    | (have j0 := eq5378 y
       grind)
    | exact resolve eq5378 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq5378
  have eq5538 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq5491
  have eq5556 : x ≠ (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq5538 eq13
    | exact resolve eq13 eq5538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5559 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq5538 eq28
    | exact resolve eq28 eq5538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5575 : x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have r₁ := eq5556
       have r₂ := eq5559
       grind)
    | exact resolve eq5556 eq5559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5556 eq5559
  have eq5580 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq5575 eq42
    | exact resolve eq42 eq5575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq5575
  have eq5586 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq5580
    | exact resolve eq5580 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5580
  have eq5589 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq5586
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5586
    | exact resolve eq5586 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5586
  have eq5597 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq5589 eq611
    | (have j0 := eq611 (σ (M.op x y)) (σ (M.op x y)) x x
       grind)
    | exact resolve eq611 eq5589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq5599 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1196 eq5597
    | (have j1 := eq1196 (σ (M.op x y)) x (σ (M.op x y)) x
       grind)
    | exact resolve eq5597 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196 eq5597
  have eq5603 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq5589 eq5599
    | exact resolve eq5599 eq5589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5599
  have eq8703 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq5603 eq752
    | exact resolve eq752 eq5603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752 eq5603
  have eq8740 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq8703
       have r₂ := eq27
       grind)
    | exact resolve eq8703 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8703
  have eq8790 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq8740 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq8740
       grind)
    | exact resolve eq13 eq8740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8740
  have eq8806 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq8790
  have eq8824 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq5589 eq8806
    | exact resolve eq8806 eq5589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5589 eq8806
  have eq41546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2560 eq1652
    | exact resolve eq1652 eq2560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560
  have eq41595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq41546
  have eq41605 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq41595
       have r₂ := eq27
       grind)
    | exact resolve eq41595 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41595
  have eq41646 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41605 eq1652
    | exact resolve eq1652 eq41605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652
  have eq41683 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by grind
  clear eq41646
  have eq41692 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq41605 eq41683
    | exact resolve eq41683 eq41605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41605 eq41683
  have eq41697 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq41692
       have r₂ := eq1645
       grind)
    | exact resolve eq41692 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645 eq41692
  have eq41993 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq41697 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq41697
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq41697
       grind)
    | exact resolve eq13 eq41697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41697
  have eq42010 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by grind
  clear eq41993
  have eq42015 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1640 eq42010
    | exact resolve eq42010 eq1640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1640 eq42010
  have eq42046 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq8824
       have i₂ := eq42015
       grind)
    | exact superpose eq42015 eq8824
    | exact resolve eq8824 eq42015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8824 eq42015
  have eq42117 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq42046
  have eq42140 : (M.op x y) = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq42117 eq29
    | exact resolve eq29 eq42117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq42175 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq42117 eq3643
    | (have r₁ := eq3643
       have r₂ := eq42117
       grind)
    | exact resolve eq3643 eq42117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3643 eq42117
  have eq42279 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq42175
  have eq42306 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq26 eq42279
    | exact resolve eq42279 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42279
  have eq42333 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq42140
    | exact resolve eq42140 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq42140
  have eq42339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq645 eq42306
    | exact resolve eq42306 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq42306
  have eq42350 : y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq42339
       have r₂ := eq27
       grind)
    | exact resolve eq42339 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42339
  have eq42357 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq42333 eq42350
    | exact resolve eq42350 eq42333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42333 eq42350
  have eq42359 : x = y ∨ x = y := by
    first
    | exact superpose eq5538 eq42357
    | exact resolve eq42357 eq5538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5538 eq42357
  have eq42360 : x = y := by grind
  clear eq42359
  have eq42362 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq42360
       grind)
    | exact superpose eq42360 eq18
    | exact resolve eq18 eq42360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq42363 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq42360
       grind)
    | exact superpose eq42360 eq24
    | exact resolve eq24 eq42360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq42360
  have eq42423 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq42363
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq42363
    | exact resolve eq42363 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42363
  have eq42424 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq42423 eq26
    | exact resolve eq26 eq42423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq42423
  have eq42677 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq42362
       grind)
    | exact superpose eq42362 eq13
    | exact resolve eq13 eq42362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42680 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq42362
       grind)
    | exact superpose eq42362 eq28
    | exact resolve eq28 eq42362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42362
  have eq42700 : (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq42677
       have r₂ := eq42680
       grind)
    | exact resolve eq42677 eq42680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42677 eq42680
  have eq43733 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq42424 eq13
    | exact resolve eq13 eq42424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43736 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42424 eq28
    | exact resolve eq28 eq42424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq42424
  have eq43753 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq43733
       have r₂ := eq43736
       grind)
    | exact resolve eq43733 eq43736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43733 eq43736
  have eq43820 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq42700
       grind)
    | exact superpose eq42700 eq40
    | exact resolve eq40 eq42700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq42700
  have eq43844 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43820
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43820
    | exact resolve eq43820 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq43820
  have eq43846 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43753 eq43844
    | exact resolve eq43844 eq43753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43753 eq43844
  have eq43848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq43846
    | exact resolve eq43846 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq43846
  have eq43850 : False := by grind
  exact eq43850

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_x_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq51 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 X1 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) X3) (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X1 (M.op X2 X0)) X3 X4 (M.op X0 x)
       have i₂ := eq14 X0 x X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 (M.op X0 x) x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X1)) ≠ X0 ∨ (k (M.op X2 (M.op X3 X0)) (M.op X0 X1)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X2 (M.op X3 X0)) (M.op X0 X1)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X2) ≠ X0 ∨ (M.op (M.op X0 (M.op X1 X0)) X2) = (k X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 (M.op X1 X0))
       have i₂ := eq14 X0 (M.op X1 X0) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op X0 (M.op X1 X0))
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq70 (σ X0)
       grind)
    | exact superpose eq70 eq10
    | exact resolve eq10 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq43
    | exact resolve eq43 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq76 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq70 sF2
       grind)
    | exact superpose eq70 eq73
    | exact resolve eq73 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq72
    | exact resolve eq72 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq81 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq95 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq96 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq97 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq70 sF3
       grind)
    | exact superpose eq70 eq96
    | exact resolve eq96 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq100 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq70 y
       grind)
    | exact superpose eq70 eq98
    | exact resolve eq98 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq111 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq112 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq89
    | (have j0 := eq89 (σ X0) (σ X1)
       grind)
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq89 y x
       grind)
    | exact superpose eq89 eq95
    | (have j1 := eq89 y x
       grind)
    | exact resolve eq95 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq129 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq127
    | exact resolve eq127 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq130 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq129
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq129
    | exact resolve eq129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq152 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq152
       have i₂ := eq70 sF1
       grind)
    | exact superpose eq70 eq152
    | exact resolve eq152 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq157 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq155
       have i₂ := eq70 sF0
       grind)
    | exact superpose eq70 eq155
    | exact resolve eq155 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq178 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq157 eq16
    | exact resolve eq16 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq193 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq89 (σ X0) sF2
       grind)
    | exact superpose eq89 eq39
    | (have j1 := eq89 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq89
    | (have j0 := eq89 (σ y) (σ x)
       grind)
    | exact resolve eq89 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq199
    | exact resolve eq199 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq203 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq200
       have r₂ := eq27
       grind)
    | exact resolve eq200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq205 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq203
    | exact resolve eq203 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq207 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205 eq27
    | exact resolve eq27 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq205 eq54
    | exact resolve eq54 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq364 eq51
    | exact resolve eq51 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq383 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq364 eq14
    | exact resolve eq14 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq382 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq382
       grind)
    | exact resolve eq12 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq405 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq401
       have r₂ := eq205
       grind)
    | exact resolve eq401 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq460 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205 eq405
    | exact resolve eq405 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq463 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq460
  have eq466 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq463 eq130
    | exact resolve eq130 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq469 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq466
  have eq631 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq469 eq67
    | exact resolve eq67 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq469
  have eq632 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq631
       have r₂ := eq205
       grind)
    | exact resolve eq631 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq632 eq130
    | exact resolve eq130 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq638
  have eq645 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq641
       have r₂ := eq27
       grind)
    | exact resolve eq641 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq648 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq645 eq29
    | exact resolve eq29 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 : G, (σ (k y X0)) = (k (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq645 eq36
    | exact resolve eq36 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq655 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq645 eq130
    | exact resolve eq130 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq668 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq655
  have eq675 : ∀ X0 : G, (σ (k y X0)) = (σ (k (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37 eq649
    | exact resolve eq649 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq649
  have eq676 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq648
    | exact resolve eq648 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq648
  have eq782 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq783 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1001 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X3 X2 X4 (M.op (M.op X0 (M.op X1 X2)) x)
       have i₂ := eq55 X2 X0 X1 x X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1073 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq112 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1184 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 (M.op X1 X2)) ∨ (M.op X0 (M.op X1 X2)) = (k (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) (M.op (M.op X0 (M.op X1 X2)) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq68 (M.op X0 (M.op X1 X2)) X2 X3 X4
       have i₂ := eq55 X2 X0 X1 X2 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq55 eq68
    | (have j0 := eq68 (M.op X0 (M.op X1 X2)) X2 X3 X4
       grind)
    | (have r₁ := eq68 (M.op X1 (M.op X2 X0)) X0 X2 X3
       have r₂ := eq55 X0 X1 X2 X0 (M.op X1 (M.op X2 X0))
       grind)
    | exact resolve eq68 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq68
  have eq1187 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (k (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) (M.op (M.op X0 (M.op X1 X2)) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq1184 X0 X1 X2 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1270 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (M.op (σ x) (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq383 eq69
    | (have r₁ := eq69 (σ x) x (σ y)
       have r₂ := eq383 (M.op x (σ x))
       grind)
    | exact resolve eq69 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq1276 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 (M.op X1 X0) X1 X0
       have i₂ := eq56 X0 X1 (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq56 eq69
    | (have r₁ := eq69 (M.op X1 X0) X1 X0
       have r₂ := eq56 X0 X1 (M.op X1 (M.op X1 X0))
       grind)
    | exact resolve eq69 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq69
  have eq1282 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1276 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1288 : ∀ X0 : G, (σ x) = (k (σ y) (M.op (σ x) (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270
  have eq1353 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq676 eq283
    | exact resolve eq283 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq3897 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (M.op X2 (M.op X3 (σ y)))) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq364 eq1001
    | exact resolve eq1001 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq4062 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (M.op X2 (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq783 eq3897
    | (have j0 := eq3897 X0 X1 X2 (σ x)
       grind)
    | exact resolve eq3897 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3897
  have eq9955 : ∀ X0 : G, (σ x) = (k (σ y) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4062 eq1288
    | exact resolve eq1288 eq4062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288 eq4062
  have eq10062 : ∀ X0 : G, (σ x) = (k (σ y) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq9955 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9955
  have eq10179 : ∀ X0 : G, (σ x) = (k (σ (M.op x y)) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq645 eq10062
    | exact resolve eq10062 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq10062
  have eq10200 : ∀ X0 : G, (σ x) = (k (σ (M.op x y)) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq10179 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10179
  have eq13686 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (k (M.op X3 X2) (M.op (M.op X0 (M.op X1 X2)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1187 X0 X1 X2 X3 x
       have i₂ := eq1001 X0 X1 X2 X3 x
       grind)
    | exact superpose eq1001 eq1187
    | exact resolve eq1187 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq1187
  have eq13978 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (k (M.op X1 y) y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq13686 y X0 y X1
       have i₂ := eq1353 (M.op X0 y)
       grind)
    | exact superpose eq1353 eq13686
    | exact resolve eq13686 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq14043 : ∀ X1 : G, (M.op y (M.op x y)) = (k (M.op X1 y) y) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq13978 x X1
       have i₂ := eq782 y x
       grind)
    | (have i₁ := eq13978 x X1
       have i₂ := eq782 y X1
       grind)
    | exact superpose eq782 eq13978
    | (have j0 := eq13978 x X1
       grind)
    | exact resolve eq13978 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13978
  have eq14194 : (k (M.op x y) y) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq283 eq14043
    | (have j0 := eq14043 x
       grind)
    | exact resolve eq14043 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14043
  have eq14232 : (σ (k y y)) = (σ (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14194 eq675
    | exact resolve eq675 eq14194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq14194
  have eq14237 : (σ (k y y)) = (σ (M.op y (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq14232
  have eq14250 : (σ (M.op y y)) = (σ (M.op y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14237
       have i₂ := eq70 y
       grind)
    | exact superpose eq70 eq14237
    | exact resolve eq14237 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq14237
  have eq14257 : (M.op (σ y) (σ y)) = (σ (M.op y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14250
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq14250
    | exact resolve eq14250 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14250
  have eq15602 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14257 eq77
    | exact resolve eq77 eq14257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq14257
  have eq15639 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53 eq15602
    | exact resolve eq15602 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq15602
  have eq15646 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq783 eq15639
    | exact resolve eq15639 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15639
  have eq15647 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15646
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15646
    | exact resolve eq15646 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15646
  have eq15675 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15647 eq10200
    | exact resolve eq10200 eq15647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10200 eq15647
  have eq15702 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq15675
  have eq15730 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15702
    | exact resolve eq15702 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15702
  have eq15740 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205 eq15730
    | exact resolve eq15730 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq15730
  have eq15752 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15740
  have eq16164 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15752 eq668
    | exact resolve eq668 eq15752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq15752
  have eq16174 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq16164
  have eq16182 : x = (M.op x y) := by
    first
    | (have r₁ := eq16174
       have r₂ := eq207
       grind)
    | exact resolve eq16174 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq16174
  have eq16185 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq16182 eq20
    | exact resolve eq20 eq16182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq16189 : x ≠ x ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq16182 eq81
    | (have r₁ := eq81
       have r₂ := eq16182
       grind)
    | exact resolve eq81 eq16182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq16197 : ∀ X0 : G, x = (M.op (M.op x X0) y) := by
    intro X0
    first
    | exact superpose eq16182 eq283
    | exact resolve eq283 eq16182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq16210 : y = (k y x) ∨ x = (M.op x x) := by grind
  clear eq16189
  have eq16220 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16185
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16185
    | exact resolve eq16185 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16185
  have eq16268 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16220 eq26
    | exact resolve eq26 eq16220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16282 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq16220 eq193
    | exact resolve eq193 eq16220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq16709 : ∀ X0 X1 : G, (M.op x (M.op X0 y)) = (k (M.op X1 y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq13686 x X0 y X1
       have i₂ := eq16197 (M.op X0 y)
       grind)
    | exact superpose eq16197 eq13686
    | exact resolve eq13686 eq16197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13686
  have eq16738 : ∀ X1 : G, x = (k y (M.op x (M.op X1 x))) := by
    intro X1
    first
    | (have i₁ := eq1282 (M.op x x) y x
       have i₂ := eq16197 x
       grind)
    | exact superpose eq16197 eq1282
    | exact resolve eq1282 eq16197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282 eq16197
  have eq16753 : ∀ X1 : G, (M.op x (M.op x y)) = (k (M.op X1 y) x) := by
    intro X1
    first
    | (have i₁ := eq16709 x X1
       have i₂ := eq782 x x
       grind)
    | (have i₁ := eq16709 x X1
       have i₂ := eq782 x X1
       grind)
    | exact superpose eq782 eq16709
    | (have j0 := eq16709 x X1
       grind)
    | exact resolve eq16709 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq16709
  have eq16765 : ∀ X1 : G, (M.op x x) = (k (M.op X1 y) x) := by
    intro X1
    first
    | exact superpose eq16182 eq16753
    | exact resolve eq16753 eq16182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16753
  have eq22286 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq16210
       grind)
    | exact superpose eq16210 eq95
    | exact resolve eq95 eq16210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16210
  have eq22307 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16220 eq22286
    | exact resolve eq22286 eq16220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22286
  have eq22319 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq22307
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22307
    | exact resolve eq22307 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22307
  have eq22443 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22319 eq89
    | (have j0 := eq89 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq89 eq22319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq22319
  have eq22455 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16268 eq22443
    | exact resolve eq22443 eq16268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22443
  have eq22459 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16268 eq22455
    | exact resolve eq22455 eq16268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22455
  have eq22462 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22459
       have r₂ := eq27
       grind)
    | exact resolve eq22459 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22459
  have eq22465 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq22462
       grind)
    | exact superpose eq22462 eq66
    | exact resolve eq66 eq22462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq22462
  have eq22521 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22465
       have r₂ := eq16182
       grind)
    | exact resolve eq22465 eq16182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22465
  have eq22525 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16182 eq22521
    | exact resolve eq22521 eq16182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22521
  have eq22544 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1073 x y
       have i₂ := eq22525
       grind)
    | exact superpose eq22525 eq1073
    | (have j0 := eq1073 x y
       grind)
    | exact resolve eq1073 eq22525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073 eq22525
  have eq22547 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22544
  have eq22554 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22547
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22547
    | exact resolve eq22547 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22547
  have eq22566 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22554
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22554
    | exact resolve eq22554 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22554
  have eq22576 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22566
    | exact resolve eq22566 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq22566
  have eq22586 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16220 eq22576
    | exact resolve eq22576 eq16220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22576
  have eq22595 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22586
       have r₂ := eq27
       grind)
    | exact resolve eq22586 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22586
  have eq22633 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq22595 eq27
    | exact resolve eq27 eq22595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59943 : (σ (k (M.op y y) x)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16282 (M.op y y)
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq16282
    | exact resolve eq16282 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq60030 : (σ (k y x)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq16282 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16282
    | (have j0 := eq16282 y
       grind)
    | exact resolve eq16282 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16282
  have eq60115 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16268 eq60030
    | exact resolve eq60030 eq16268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60030
  have eq60138 : (σ (k (M.op y y) x)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq783 eq59943
    | exact resolve eq59943 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59943
  have eq60142 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq60115
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq60115
    | exact resolve eq60115 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq60115
  have eq60159 : (M.op (σ (M.op x y)) (σ y)) = (σ (k (M.op y y) x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq22595 eq60138
    | exact resolve eq60138 eq22595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60138
  have eq60161 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16220 eq60142
    | exact resolve eq60142 eq16220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60142
  have eq60171 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq60159
       have i₂ := eq16765 y
       grind)
    | exact superpose eq16765 eq60159
    | exact resolve eq60159 eq16765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16765 eq60159
  have eq60172 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq22595 eq60161
    | exact resolve eq60161 eq22595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60161
  have eq60180 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq16268 eq60171
    | exact resolve eq60171 eq16268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60171
  have eq60181 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq16268 eq60172
    | exact resolve eq60172 eq16268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60172
  have eq60189 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq60180
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq60180
    | exact resolve eq60180 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq60180
  have eq60190 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq60181
       have r₂ := eq27
       grind)
    | exact resolve eq60181 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60181
  have eq60197 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq16220 eq60189
    | exact resolve eq60189 eq16220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60189
  have eq60202 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq22595 eq60197
    | exact resolve eq60197 eq22595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60197
  have eq60207 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq783 eq60202
    | exact resolve eq60202 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783 eq60202
  have eq60210 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22595 eq60207
    | exact resolve eq60207 eq22595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22595 eq60207
  have eq60212 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq16268 eq60210
    | exact resolve eq60210 eq16268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16268 eq60210
  have eq60213 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq60212
       have r₂ := eq27
       grind)
    | exact resolve eq60212 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq60212
  have eq60220 : (τ (σ y)) = (k y (M.op x y)) := by
    first
    | exact superpose eq60190 eq111
    | exact resolve eq111 eq60190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq60190
  have eq60263 : (τ (σ y)) = (k y x) := by
    first
    | exact superpose eq16182 eq60220
    | exact resolve eq60220 eq16182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60220
  have eq60267 : y = (k y x) := by
    first
    | exact superpose eq29 eq60263
    | exact resolve eq60263 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60263
  have eq60268 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq60213 eq178
    | exact resolve eq178 eq60213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq60213
  have eq60364 : (τ (σ y)) = (M.op x x) := by
    first
    | exact superpose eq16182 eq60268
    | exact resolve eq60268 eq16182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60268
  have eq60386 : y = (M.op x x) := by
    first
    | exact superpose eq29 eq60364
    | exact resolve eq60364 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq60364
  have eq60762 : x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq16738 x
       have i₂ := eq60386
       grind)
    | exact superpose eq60386 eq16738
    | exact resolve eq16738 eq60386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16738 eq60386
  have eq60844 : x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq60762
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60762
    | exact resolve eq60762 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq60762
  have eq60880 : x = (k y x) := by
    first
    | exact superpose eq16182 eq60844
    | exact resolve eq60844 eq16182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16182 eq60844
  have eq60904 : x = y := by
    first
    | (have i₁ := eq60880
       have i₂ := eq60267
       grind)
    | exact superpose eq60267 eq60880
    | exact resolve eq60880 eq60267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60267 eq60880
  have eq60926 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq60904
       grind)
    | exact superpose eq60904 eq24
    | exact resolve eq24 eq60904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq60904
  have eq61098 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq60926
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq60926
    | exact resolve eq60926 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq60926
  have eq61138 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16220 eq61098
    | exact resolve eq61098 eq16220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16220 eq61098
  have eq61166 : False := by grind
  exact eq61166

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pxx_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
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
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq39
    | exact resolve eq39 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq39
  have eq61 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq66 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq61
    | (have j0 := eq61 X0 X1
       grind)
    | exact resolve eq61 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq91 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq66
    | exact resolve eq66 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq704 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq677 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq677
    | (have j0 := eq677 X0 X1
       grind)
    | exact resolve eq677 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq677
  have eq710 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq704 X0 X1
       have j1 := eq91 X1 X0
       grind)
    | (have r₁ := eq704 X1 X0
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq704 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq704 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq704
  have eq717 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq710 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq710
    | exact resolve eq710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq710 (σ X1) X0
       grind)
    | exact superpose eq710 eq15
    | (have j1 := eq710 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq737 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq717 (τ X0) X1
       grind)
    | exact superpose eq717 eq19
    | (have j1 := eq717 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq717
  have eq1606 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq737 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq737
    | exact resolve eq737 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq1653 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1606 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1606
    | (have j0 := eq1606 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq1606 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606
  have eq10429 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq727 x y
       grind)
    | exact superpose eq727 eq16
    | (have j1 := eq727 x y
       grind)
    | exact resolve eq16 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq10716 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10429
       have i₂ := eq1653 x y
       grind)
    | exact superpose eq1653 eq10429
    | (have j1 := eq1653 (σ x) (σ y)
       grind)
    | (have r₁ := eq10429
       have r₂ := eq1653 x y
       grind)
    | (have r₁ := eq10429
       have r₂ := eq1653 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq10429
       have r₂ := eq1653 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq10429 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653 eq10429
  have eq10717 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq10716
  have eq10720 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10717
       grind)
    | exact superpose eq10717 eq16
    | exact resolve eq16 eq10717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10717
  have eq10721 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq10720
       have r₂ := eq44 x
       grind)
    | exact resolve eq10720 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10720
  have eq11102 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10721
       grind)
    | exact superpose eq10721 eq16
    | exact resolve eq16 eq10721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11103 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10721
       grind)
    | exact superpose eq10721 eq10
    | exact resolve eq10 eq10721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10721
  have eq11164 : x = y := by
    first
    | (have i₁ := eq11103
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11103
    | exact resolve eq11103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11103
  have eq11165 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11102
       have i₂ := eq44 x
       grind)
    | exact superpose eq44 eq11102
    | exact resolve eq11102 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq11102
  have eq11166 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11165
       have i₂ := eq11164
       grind)
    | exact superpose eq11164 eq11165
    | exact resolve eq11165 eq11164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11164 eq11165
  have eq11167 : False := by grind
  exact eq11167

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_pyx_pxy_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq31 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq9 X0 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X4) X0) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 (M.op X1 X0) X4 (M.op X0 x) x
       have i₂ := eq9 X0 x x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq69 : ∀ X0 X1 X2 X4 : G, (M.op X2 (M.op X1 X0)) = (M.op X2 (M.op X4 X0)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq31 X2 (M.op X1 X0) X4 (M.op X0 x)
       have i₂ := eq9 X0 x X2 X1
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq183 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq202 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq183 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq202 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq202
    | (have j0 := eq202 (σ X0) (σ X1)
       grind)
    | exact resolve eq202 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq202 X0 (τ X1)
       grind)
    | exact superpose eq202 eq20
    | (have j1 := eq202 X0 (τ X1)
       grind)
    | exact resolve eq20 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq230 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq202
  have eq305 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq230 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq306 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq305 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq310 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq306 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq306
    | exact resolve eq306 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq306 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq306
    | exact resolve eq306 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq312 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq311 X0
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq311
    | exact resolve eq311 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq313 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq310 X0
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq310
    | exact resolve eq310 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq310
  have eq339 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X2 (M.op X1 (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X2 X1
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq9
    | exact resolve eq9 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X0) (σ X0) x
       have i₂ := eq313 X0
       grind)
    | exact superpose eq313 eq33
    | exact resolve eq33 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq635 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq339 X0 (τ X0) X1
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq339
    | exact resolve eq339 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq339
  have eq1259 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X1 X0))) = (M.op (τ X0) (M.op X2 (τ X0))) := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    have f1259_11 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (M.op X1 (τ (M.op X0 X0)))) := by
      intro X0 X1
      grind
    have f1259_13 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
      intro X0 X1 X2 X3
      grind
    have f1259_20 : (τ (M.op X0 (M.op X1 X0))) ≠ (M.op (τ X0) (M.op X2 (τ X0))) := by grind
    have f1259_28 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
      intro X0 X1 X4 X5
      first
      | (have i₁ := f1259_13 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
         have i₂ := f1259_13 X0 X1 x x
         grind)
      | exact superpose f1259_13 f1259_13
      | exact resolve f1259_13 f1259_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1259_50 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X1 X0))) = (M.op (τ X0) (M.op X2 (τ X0))) := by
      intro X0 X1 X2
      first
      | (have i₁ := f1259_11 (M.op X2 (M.op x X2)) X1
         have i₂ := f1259_13 X2 (M.op x X2) X2 x
         grind)
      | exact superpose f1259_13 f1259_11
      | exact resolve f1259_11 f1259_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1259_146 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f1259_28 X1 (M.op X2 X0) X3 (M.op X0 x)
         have i₂ := f1259_13 X0 x X1 X2
         grind)
      | exact superpose f1259_13 f1259_28
      | exact resolve f1259_28 f1259_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1259_274 : ∀ X0 : G, (τ (M.op X0 (M.op X1 X0))) ≠ (M.op (τ X0) (M.op X0 (τ X0))) := by
      intro X0
      first
      | (have i₁ := f1259_20
         have i₂ := f1259_146 (τ X0) (τ X0) X2 X0
         grind)
      | (have i₁ := f1259_20
         have i₂ := f1259_146 (τ X0) (τ X0) X0 X2
         grind)
      | exact superpose f1259_146 f1259_20
      | exact resolve f1259_20 f1259_146
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1259_279 : False := by
      first
      | (have r₁ := f1259_274 x
         have r₂ := f1259_50 X0 X1 x
         grind)
      | exact resolve f1259_274 f1259_50
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f1259_279
  clear eq635
  have eq2275 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (τ (M.op (σ X0) (M.op X2 (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1259 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1259
    | exact resolve eq1259 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq6567 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq213 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq213
    | exact resolve eq213 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq6830 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6567 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq6567
    | (have j0 := eq6567 X0 X1
       grind)
    | exact resolve eq6567 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6567
  have eq11015 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 X1
       have i₂ := eq313 X0
       grind)
    | exact superpose eq313 eq204
    | (have j0 := eq204 X0 X1
       grind)
    | exact resolve eq204 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq313
  have eq11359 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq11015 X0 X1
       grind)
    | (have i₁ := eq10 X1
       have i₂ := eq11015 X0 X1
       grind)
    | exact superpose eq11015 eq10
    | (have j1 := eq11015 X0 X1
       grind)
    | exact resolve eq10 eq11015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11015
  have eq11464 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11359 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq11359
    | (have j0 := eq11359 X0 X1
       grind)
    | exact resolve eq11359 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11359
  have eq11718 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11464 x y
       grind)
    | exact superpose eq11464 eq16
    | (have j1 := eq11464 x y
       grind)
    | exact resolve eq16 eq11464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11464
  have eq11774 : y = (M.op x x) := by
    first
    | (have j1 := eq6830 y x
       grind)
    | (have r₁ := eq11718
       have r₂ := eq6830 y x
       grind)
    | exact resolve eq11718 eq6830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6830 eq11718
  have eq11799 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq364 x x
       have i₂ := eq11774
       grind)
    | exact superpose eq11774 eq364
    | exact resolve eq364 eq11774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq11823 : ∀ X0 X1 : G, (M.op X1 (M.op X0 x)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq69 x x X1 X0
       have i₂ := eq11774
       grind)
    | exact superpose eq11774 eq69
    | exact resolve eq69 eq11774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq11774
  have eq13469 : ∀ X1 : G, (τ (M.op (σ x) (σ y))) = (M.op x (M.op X1 x)) := by
    intro X1
    first
    | (have i₁ := eq2275 x X1 (M.op (σ y) x)
       have i₂ := eq11799 x
       grind)
    | exact superpose eq11799 eq2275
    | exact resolve eq2275 eq11799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275 eq11799
  have eq13516 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13469 x
       have i₂ := eq11823 x x
       grind)
    | exact superpose eq11823 eq13469
    | exact resolve eq13469 eq11823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11823 eq13469
  have eq16071 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq13516
       grind)
    | exact superpose eq13516 eq11
    | exact resolve eq11 eq13516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13516
  have eq16096 : False := by grind
  exact eq16096

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq9 X0 X1 x x
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
  have eq36 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq80 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq99 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq413 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq80 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq80 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq80 X1 X1
       grind)
    | exact resolve eq13 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq425 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq413 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq426 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq429 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq426 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq426
    | (have j0 := eq426 X0 X1
       grind)
    | exact resolve eq426 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq434 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq429 X0 X1
       have j1 := eq424 X0 X1
       grind)
    | (have r₁ := eq429 X0 X1
       have r₂ := eq424 X0 X1
       grind)
    | (have r₁ := eq429 X0 (k X1 X0)
       have r₂ := eq424 X0 X1
       grind)
    | (have r₁ := eq429 X0 X0
       have r₂ := eq424 X0 X0
       grind)
    | exact resolve eq429 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424 eq429
  have eq693 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op X1 (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0
       have i₂ := eq99 (τ X0) (τ X0) (τ X0) X1
       grind)
    | (have i₁ := eq36 X0
       have i₂ := eq99 (τ X0) (τ X0) X1 (τ X0)
       grind)
    | exact superpose eq99 eq36
    | exact resolve eq36 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq99
  have eq1126 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq434 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq434
    | exact resolve eq434 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq434 x y
       grind)
    | exact superpose eq434 eq16
    | (have j1 := eq434 x y
       grind)
    | exact resolve eq16 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq1166 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1126 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1126
    | (have j0 := eq1126 X0 X1
       grind)
    | exact resolve eq1126 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1126
  have eq1167 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1166 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1166
    | exact resolve eq1166 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq1228 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq1167 (τ X1) X0
       grind)
    | exact superpose eq1167 eq18
    | (have j1 := eq1167 (τ X1) X0
       grind)
    | exact resolve eq18 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1167
  have eq1470 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1228 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1228
    | exact resolve eq1228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1516 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1470 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1470
    | (have j0 := eq1470 X0 X1
       grind)
    | exact resolve eq1470 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1872 : ∀ X0 X1 : G, (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) = (τ (σ (M.op (τ (σ X0)) (M.op X1 (τ (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq693 (σ X0) X1
       grind)
    | exact superpose eq693 eq26
    | exact resolve eq26 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq693
  have eq1908 : ∀ X0 X1 : G, (M.op (τ (σ X0)) (M.op X1 (τ (σ X0)))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1872 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) (M.op X1 (τ (σ X0))))
       grind)
    | exact superpose eq10 eq1872
    | exact resolve eq1872 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1872
  have eq1937 : ∀ X0 X1 : G, (M.op (τ (σ X0)) (M.op X1 (τ (σ X0)))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1908 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq1908
    | exact resolve eq1908 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908
  have eq1959 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1937 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1937
    | exact resolve eq1937 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937
  have eq2629 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1140
       have i₂ := eq1516 y x
       grind)
    | exact superpose eq1516 eq1140
    | (have j1 := eq1516 (σ y) (σ x)
       grind)
    | (have r₁ := eq1140
       have r₂ := eq1516 y x
       grind)
    | exact resolve eq1140 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2630 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2629
  have eq2660 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1959 x x
       have i₂ := eq2630
       grind)
    | exact superpose eq2630 eq1959
    | exact resolve eq1959 eq2630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2630
  have eq2787 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1140
       have i₂ := eq2660
       grind)
    | exact superpose eq2660 eq1140
    | exact resolve eq1140 eq2660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140 eq2660
  have eq2788 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2787
  have eq2789 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2788
  have eq2900 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1959 (σ x) (σ x)
       have i₂ := eq2789
       grind)
    | exact superpose eq2789 eq1959
    | exact resolve eq1959 eq2789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2789
  have eq2904 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq2900
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2900
    | exact resolve eq2900 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2900
  have eq2980 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2904
       grind)
    | exact superpose eq2904 eq16
    | exact resolve eq16 eq2904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2904
  have eq3021 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2980
       have i₂ := eq1516 y x
       grind)
    | exact superpose eq1516 eq2980
    | (have j1 := eq1516 y x
       grind)
    | (have r₁ := eq2980
       have r₂ := eq1516 y x
       grind)
    | exact resolve eq2980 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516
  have eq3022 : y = (M.op x x) := by grind
  clear eq3021
  have eq3107 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1959 x x
       have i₂ := eq3022
       grind)
    | exact superpose eq3022 eq1959
    | exact resolve eq1959 eq3022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959 eq3022
  have eq3226 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2980
       have i₂ := eq3107
       grind)
    | exact superpose eq3107 eq2980
    | exact resolve eq2980 eq3107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2980 eq3107
  have eq3229 : False := by grind
  exact eq3229

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq51 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 X1 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 X1 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) X3) (M.op X4 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X1 (M.op X2 X0)) X3 X4 (M.op X0 x)
       have i₂ := eq14 X0 x X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    grind
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq77 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
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
  have eq78 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq113
    | exact resolve eq113 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq114
    | exact resolve eq114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq219 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq802 : ∀ X0 X1 X2 X3 : G, (k (M.op X3 X2) (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2)))) = (M.op (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2))) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq67 (M.op x X0) (M.op (M.op X1 (M.op X2 X0)) X3)
       have i₂ := eq56 X0 X1 X2 X3 x
       grind)
    | exact superpose eq56 eq67
    | exact resolve eq67 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq67
  have eq866 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq8914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8915 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8914
    | exact resolve eq8914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8914
  have eq8926 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq8915
       have r₂ := eq28
       grind)
    | exact resolve eq8915 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8915
  have eq8928 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8926
    | exact resolve eq8926 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8926
  have eq8931 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq8928
  have eq8955 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8931
    | exact resolve eq8931 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8931
  have eq8962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8955 eq115
    | exact resolve eq115 eq8955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8955
  have eq8971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8962
  have eq8973 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8971
       have r₂ := eq28
       grind)
    | exact resolve eq8971 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8971
  have eq8977 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8973
  have eq9001 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8977
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8977
    | exact resolve eq8977 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8977
  have eq9005 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq9001
       grind)
    | exact superpose eq9001 eq74
    | exact resolve eq74 eq9001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9001
  have eq9021 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq9005
    | exact resolve eq9005 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9005
  have eq9236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9021 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq9021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9239 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq9236
    | exact resolve eq9236 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9236
  have eq9250 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9239
       have r₂ := eq28
       grind)
    | exact resolve eq9239 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9239
  have eq9252 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq9250
    | exact resolve eq9250 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9250
  have eq9253 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9252
  have eq9257 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9253
  have eq9284 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq9257
    | exact resolve eq9257 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9257
  have eq9299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9284 eq9021
    | exact resolve eq9021 eq9284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9021 eq9284
  have eq9302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9299
  have eq9306 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq9302
       have r₂ := eq28
       grind)
    | exact resolve eq9302 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9302
  have eq9308 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9306 eq28
    | exact resolve eq28 eq9306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9311 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9306 eq78
    | (have r₁ := eq78
       have r₂ := eq9306
       grind)
    | exact resolve eq78 eq9306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq9306
  have eq9320 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq9311
  have eq16711 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9320 eq115
    | exact resolve eq115 eq9320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16735 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq16711
  have eq16749 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16735
       have r₂ := eq9308
       grind)
    | exact resolve eq16735 eq9308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16735
  have eq16758 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq16749
  have eq16788 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq16758
    | exact resolve eq16758 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16758
  have eq16849 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16788 eq115
    | exact resolve eq115 eq16788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq16788
  have eq16869 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq16849
  have eq16873 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16869
       have r₂ := eq28
       grind)
    | exact resolve eq16869 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16869
  have eq16878 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq16873
  have eq16907 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16878
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16878
    | exact resolve eq16878 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq16878
  have eq16911 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq16907
       grind)
    | exact superpose eq16907 eq74
    | exact resolve eq74 eq16907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16907
  have eq16941 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq16911
    | exact resolve eq16911 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16911
  have eq17341 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16941 eq9320
    | exact resolve eq9320 eq16941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9320
  have eq17353 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq17341
  have eq17361 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17353
       have r₂ := eq9308
       grind)
    | exact resolve eq17353 eq9308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9308 eq17353
  have eq17380 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq17361
  have eq17412 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq17380
    | exact resolve eq17380 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17380
  have eq17434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17412 eq16941
    | exact resolve eq16941 eq17412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16941 eq17412
  have eq17444 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17434
  have eq17452 : y = (M.op x y) := by
    first
    | (have r₁ := eq17444
       have r₂ := eq28
       grind)
    | exact resolve eq17444 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17444
  have eq17454 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq17452 eq21
    | exact resolve eq21 eq17452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq17456 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | exact superpose eq17452 eq51
    | exact resolve eq51 eq17452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq17461 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq17452 eq77
    | (have r₁ := eq77
       have r₂ := eq17452
       grind)
    | exact resolve eq77 eq17452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq17503 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | exact superpose eq17452 eq219
    | exact resolve eq219 eq17452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq17452
  have eq17517 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq17461
  have eq17572 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq17454
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17454
    | exact resolve eq17454 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17454
  have eq18407 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq17572 eq27
    | exact resolve eq27 eq17572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq20994 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq17517
       grind)
    | exact superpose eq17517 eq74
    | exact resolve eq74 eq17517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21012 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq866 x y
       have i₂ := eq17517
       grind)
    | exact superpose eq17517 eq866
    | (have j0 := eq866 x y
       grind)
    | exact resolve eq866 eq17517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17517
  have eq21015 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq21012
  have eq21024 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21015
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21015
    | exact resolve eq21015 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21015
  have eq21040 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17572 eq20994
    | exact resolve eq20994 eq17572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20994
  have eq21044 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17572 eq21024
    | exact resolve eq21024 eq17572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21024
  have eq21059 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21040
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21040
    | exact resolve eq21040 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21040
  have eq21062 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21044
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21044
    | exact resolve eq21044 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21044
  have eq21076 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17572 eq21059
    | exact resolve eq21059 eq17572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21059
  have eq21079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18407 eq21062
    | exact resolve eq21062 eq18407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21062
  have eq21090 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq21079
       have r₂ := eq28
       grind)
    | exact resolve eq21079 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21079
  have eq21101 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21090
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21090
    | exact resolve eq21090 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21090
  have eq21112 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21101
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21101
    | exact resolve eq21101 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21101
  have eq21123 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17572 eq21112
    | exact resolve eq21112 eq17572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21112
  have eq21238 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq21123
  have eq21273 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18407 eq21238
    | exact resolve eq21238 eq18407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21238
  have eq21289 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21273 eq21076
    | exact resolve eq21076 eq21273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21076 eq21273
  have eq21301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq21289
  have eq21303 : y = (M.op x x) := by
    first
    | (have r₁ := eq21301
       have r₂ := eq28
       grind)
    | exact resolve eq21301 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21301
  have eq21338 : ∀ X0 X1 : G, (k y (M.op y (M.op X0 (M.op X1 x)))) = (M.op (M.op y (M.op X0 (M.op X1 x))) y) := by
    intro X0 X1
    first
    | (have i₁ := eq802 X0 X1 x x
       have i₂ := eq21303
       grind)
    | exact superpose eq21303 eq802
    | exact resolve eq802 eq21303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802 eq21303
  have eq21341 : ∀ X0 X1 : G, y = (k y (M.op y (M.op X0 (M.op X1 x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq21338 X0 X1
       have i₂ := eq17503 (M.op X0 (M.op X1 x))
       grind)
    | exact superpose eq17503 eq21338
    | exact resolve eq21338 eq17503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17503 eq21338
  have eq21356 : y = (k y x) := by
    first
    | (have i₁ := eq21341 x x
       have i₂ := eq17456 x x
       grind)
    | exact superpose eq17456 eq21341
    | exact resolve eq21341 eq17456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17456 eq21341
  have eq21385 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq21356
       grind)
    | exact superpose eq21356 eq74
    | exact resolve eq74 eq21356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq21403 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq866 x y
       have i₂ := eq21356
       grind)
    | exact superpose eq21356 eq866
    | (have j0 := eq866 x y
       grind)
    | exact resolve eq866 eq21356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866 eq21356
  have eq21406 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq21403
  have eq21415 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21406
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21406
    | exact resolve eq21406 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21406
  have eq21430 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq17572 eq21385
    | exact resolve eq21385 eq17572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21385
  have eq21433 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17572 eq21415
    | exact resolve eq21415 eq17572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21415
  have eq21448 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq21430
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21430
    | exact resolve eq21430 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21430
  have eq21451 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21433
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21433
    | exact resolve eq21433 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21433
  have eq21465 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq17572 eq21448
    | exact resolve eq21448 eq17572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21448
  have eq21468 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18407 eq21451
    | exact resolve eq21451 eq18407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21451
  have eq21479 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq21468
       have r₂ := eq28
       grind)
    | exact resolve eq21468 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21468
  have eq21490 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21479
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21479
    | exact resolve eq21479 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21479
  have eq21501 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21490
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21490
    | exact resolve eq21490 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq21490
  have eq21512 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17572 eq21501
    | exact resolve eq21501 eq17572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17572 eq21501
  have eq21711 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq21512
  have eq21742 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq18407 eq21711
    | exact resolve eq21711 eq18407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18407 eq21711
  have eq21745 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21465 eq21742
    | exact resolve eq21742 eq21465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21465 eq21742
  have eq21747 : False := by grind
  exact eq21747

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pxx_pxy_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq13 X0 (M.op X0 X0)
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
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
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
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
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
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
  have eq185 : ∀ X2 X3 : G, (M.op x y) = (M.op x (M.op X2 (M.op X3 (M.op x y)))) := by
    intro X2 X3
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
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
  have eq189 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq28 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X3 (k X0 X1))) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X2 X3 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X1) (M.op X2 (M.op X3 X0))) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2 X3
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X1 (k X0 (σ x)))) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X0
       have i₂ := eq28 X0 sF2
       grind)
    | exact superpose eq28 eq176
    | (have j1 := eq28 X0 (σ x)
       grind)
    | exact resolve eq176 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621 : (M.op x y) = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
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
  have eq632 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq599 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq599 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq599 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq634 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq621
       grind)
    | exact superpose eq621 eq41
    | exact resolve eq41 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq634
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq634
    | exact resolve eq634 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq637 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
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
    | (have j1 := eq28 x y
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
  have eq661 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq654 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (M.op X0 (M.op X1 (σ x)))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq654 eq16
    | exact resolve eq16 eq654
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
  clear eq668
  have eq692 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq654 eq682
    | exact resolve eq682 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq720
  have eq734 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq729 eq179
    | exact resolve eq179 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq761 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq661 eq98
    | exact resolve eq98 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq768 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq761
    | exact resolve eq761 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq886 : (τ (σ y)) = (k x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq658 eq98
    | exact resolve eq98 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq886
    | exact resolve eq886 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq901 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq894 eq682
    | exact resolve eq682 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq907 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq894 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq894
       grind)
    | exact resolve eq13 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq911 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | (have j0 := eq907 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq915 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ y = (k x x) := by grind
  clear eq901
  have eq1041 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (M.op X0 (M.op X2 (M.op X3 (k X0 X1)))) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X0 X1 x x
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1077 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq16 X0 x X1 X2
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1078 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq178 eq177
    | exact resolve eq177 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1080 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq179 eq177
    | exact resolve eq177 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1088 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq734 eq177
    | exact resolve eq177 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq1163 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X3 X0)) = (M.op X1 (k X2 X0)) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X1 (k X2 X0) X3 (M.op X0 x)
       have i₂ := eq601 X2 X0 x X1
       grind)
    | exact superpose eq601 eq177
    | (have j1 := eq601 X2 X0 X2 X3
       grind)
    | exact resolve eq177 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1439 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq911 eq894
    | exact resolve eq894 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq911
  have eq1456 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (k x x) := by grind
  clear eq1439
  have eq1521 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x x) ∨ y = (k x x) := by
    first
    | exact superpose eq1456 eq142
    | exact resolve eq142 eq1456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456
  have eq1535 : y = (k x x) ∨ y = (M.op x x) ∨ x = (k x x) := by
    first
    | exact superpose eq30 eq1521
    | exact resolve eq1521 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq1541 : x ≠ y ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq631 x
       have i₂ := eq1535
       grind)
    | exact superpose eq1535 eq631
    | (have j0 := eq631 x
       grind)
    | (have r₁ := eq631 x
       have r₂ := eq1535
       grind)
    | exact resolve eq631 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1542 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq601 x x X0 X1
       have i₂ := eq1535
       grind)
    | exact superpose eq1535 eq601
    | (have j0 := eq601 x x x x
       grind)
    | exact resolve eq601 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1544 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq1542 X0 X1
       have j1 := eq631 x
       grind)
    | (have r₁ := eq1542 X0 X1
       have r₂ := eq631 x
       grind)
    | exact resolve eq1542 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq1545 : x ≠ y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq631 x
       grind)
    | (have r₁ := eq1541
       have r₂ := eq631 x
       grind)
    | exact resolve eq1541 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541
  have eq1548 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1544 X0 x
       have i₂ := eq1078 (M.op x X0) x
       grind)
    | (have i₁ := eq1544 X0 x
       have i₂ := eq1078 (M.op x X0) x
       grind)
    | exact superpose eq1078 eq1544
    | (have j0 := eq1544 X0 x
       grind)
    | exact resolve eq1544 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1551 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x x) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq28 eq1548
    | (have j0 := eq1548 X0
       have j1 := eq28 x x
       grind)
    | exact resolve eq1548 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1997 : y = (k x x) ∨ x = (M.op x x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq185 eq1551
    | (have j0 := eq1551 y
       grind)
    | exact resolve eq1551 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq2021 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq601 x x X0 X1
       have i₂ := eq1997
       grind)
    | exact superpose eq1997 eq601
    | (have j0 := eq601 x x x x
       grind)
    | exact resolve eq601 eq1997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601 eq1997
  have eq2022 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op X1 y)) ∨ x = (M.op x x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | (have j0 := eq2021 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021
  have eq2024 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2022 X0 x
       have i₂ := eq1078 (M.op x X0) x
       grind)
    | (have i₁ := eq2022 X0 x
       have i₂ := eq1078 (M.op x X0) x
       grind)
    | exact superpose eq1078 eq2022
    | (have j0 := eq2022 X0 x
       grind)
    | exact resolve eq2022 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022
  have eq2655 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq185 eq2024
    | (have j0 := eq2024 y
       grind)
    | exact resolve eq2024 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024
  have eq2677 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq2655
  have eq2680 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2677
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq2677
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq2677 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2682 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2677 eq185
    | exact resolve eq185 eq2677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2683 : ∀ X0 : G, y = (M.op (M.op y X0) x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2677 eq178
    | exact resolve eq178 eq2677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2687 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op X1 x)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq2677 eq16
    | exact resolve eq16 eq2677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2688 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2677 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq2677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2703 : ∀ X0 : G, x = (M.op (k x X0) (M.op x y)) ∨ (M.op x x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq602 x X0 x x
       have i₂ := eq2682 x
       grind)
    | exact superpose eq2682 eq602
    | (have j0 := eq602 x X0 x x
       grind)
    | exact resolve eq602 eq2682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2704 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op X1 (M.op x y))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 x X1 x
       have i₂ := eq2682 X0
       grind)
    | exact superpose eq2682 eq177
    | exact resolve eq177 eq2682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2682
  have eq2721 : ∀ X0 : G, x = (M.op (k x X0) (M.op x y)) ∨ (k x x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28 eq2703
    | (have j0 := eq2703 X0
       have j1 := eq28 x x
       grind)
    | exact resolve eq2703 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703
  have eq3185 : x = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq2721 x
       have i₂ := eq1535
       grind)
    | exact superpose eq1535 eq2721
    | (have j0 := eq2721 x
       grind)
    | exact resolve eq2721 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq3205 : x = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq631 x
       grind)
    | (have r₁ := eq3185
       have r₂ := eq631 x
       grind)
    | exact resolve eq3185 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3185
  have eq3208 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq3205
       have r₂ := eq1545
       grind)
    | exact resolve eq3205 eq1545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545 eq3205
  have eq3211 : y = (k x x) ∨ x = (M.op x x) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq28 eq3208
    | (have j1 := eq28 x x
       grind)
    | exact resolve eq3208 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3208
  have eq3213 : x = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq2721 x
       have i₂ := eq3211
       grind)
    | exact superpose eq3211 eq2721
    | exact resolve eq2721 eq3211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2721
  have eq3218 : x ≠ y ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq631 x
       have i₂ := eq3211
       grind)
    | exact superpose eq3211 eq631
    | (have j0 := eq631 x
       grind)
    | exact resolve eq631 eq3211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3211
  have eq3223 : x ≠ y ∨ x = (M.op x x) ∨ x = (M.op y (M.op x y)) := by grind
  clear eq3218
  have eq3225 : x = (M.op y (M.op x y)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq3213
  have eq3231 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq3225
       have r₂ := eq3223
       grind)
    | exact resolve eq3225 eq3223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3223 eq3225
  have eq3237 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3231 eq2683
    | exact resolve eq2683 eq3231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683
  have eq3239 : ∀ X0 : G, y = (M.op x (M.op X0 (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3231 eq178
    | exact resolve eq178 eq3231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3244 : (M.op x y) = (M.op y y) ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3231 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq3231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3231
  have eq3252 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq3237
  have eq3468 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op (M.op x y) x) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2687 eq692
    | exact resolve eq692 eq2687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2687
  have eq3473 : x = (M.op x x) ∨ x = (k (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2677 eq692
    | exact resolve eq692 eq2677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3475 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq654 eq692
    | exact resolve eq692 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3496 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq664 (M.op sF2 sF2) sF2
       have i₂ := eq692 sF2
       grind)
    | exact superpose eq692 eq664
    | (have j1 := eq692 (σ x)
       grind)
    | exact resolve eq664 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq3515 : x = (k (M.op x y) x) ∨ x = (M.op x x) := by grind
  clear eq3473
  have eq3520 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq654 eq3496
    | exact resolve eq3496 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3496
  have eq3530 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq637 eq3475
    | exact resolve eq3475 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3475
  have eq3535 : (M.op x y) = (k (M.op (M.op x y) x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2677 eq3468
    | exact resolve eq3468 eq2677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468
  have eq3539 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq654 eq3520
    | exact resolve eq3520 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq3520
  have eq3546 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq637 eq3539
    | exact resolve eq3539 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3539
  have eq3550 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3515 eq38
    | exact resolve eq38 eq3515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq3515
  have eq3557 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3550
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3550
    | exact resolve eq3550 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3550
  have eq3586 : y = (k x x) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq3252
       grind)
    | exact superpose eq3252 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq3252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3595 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq3252
  have eq3599 : y = (k x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq3586
       have r₂ := eq3595
       grind)
    | exact resolve eq3586 eq3595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3586
  have eq3610 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq3599
       grind)
    | exact superpose eq3599 eq40
    | exact resolve eq40 eq3599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3623 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3610
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3610
    | exact resolve eq3610 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3610
  have eq3625 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3623
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3623
    | exact resolve eq3623 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3623
  have eq3639 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3625 eq631
    | (have j0 := eq631 (σ x)
       grind)
    | exact resolve eq631 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3640 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (M.op X0 (M.op X1 (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq3625 eq602
    | (have j0 := eq602 (σ x) (σ x) x x
       grind)
    | exact resolve eq602 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3643 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (k (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1163 eq3640
    | (have j1 := eq1163 (σ x) x (σ x) x
       grind)
    | exact resolve eq3640 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3640
  have eq3647 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3625 eq3643
    | exact resolve eq3643 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3625 eq3643
  have eq3650 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1080 eq3647
    | (have j0 := eq3647 (σ x)
       grind)
    | exact resolve eq3647 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3647
  have eq3659 : y = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2680 eq3239
    | exact resolve eq3239 eq2680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2680 eq3239
  have eq3689 : y = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq3659
  have eq3701 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2688 eq3689
    | exact resolve eq3689 eq2688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2688 eq3689
  have eq3703 : x = y ∨ x = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2677 eq3701
    | exact resolve eq3701 eq2677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3701
  have eq3704 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq3703
       have r₂ := eq3595
       grind)
    | exact resolve eq3703 eq3595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3703
  have eq3708 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3704 eq42
    | exact resolve eq42 eq3704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704
  have eq3715 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq3708
    | exact resolve eq3708 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3708
  have eq3717 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3715
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3715
    | exact resolve eq3715 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3715
  have eq3738 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3530 eq1088
    | exact resolve eq1088 eq3530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq3745 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3530 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq3530
       grind)
    | exact resolve eq13 eq3530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3756 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq3745 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3745
  have eq3761 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq3738 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3738
  have eq3776 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq3756 eq3761
    | exact resolve eq3761 eq3756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3761
  have eq3781 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3546 eq3530
    | exact resolve eq3530 eq3546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3546
  have eq3813 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq3781
  have eq3831 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq175 X0 x
       have i₂ := eq3813
       grind)
    | exact superpose eq3813 eq175
    | exact resolve eq175 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq3835 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x x X0 X1
       have i₂ := eq3813
       grind)
    | exact superpose eq3813 eq16
    | exact resolve eq16 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3837 : y = (k x x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq3813
       grind)
    | exact superpose eq3813 eq28
    | exact resolve eq28 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3849 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3831 x
       have i₂ := eq1078 sF0 x
       grind)
    | (have i₁ := eq3831 x
       have i₂ := eq1078 sF0 x
       grind)
    | exact superpose eq1078 eq3831
    | (have j0 := eq3831 x
       grind)
    | exact resolve eq3831 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3831
  have eq3851 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3849
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq3849
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq3849 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3856 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq3849 eq185
    | exact resolve eq185 eq3849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq4848 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq3837
       grind)
    | exact superpose eq3837 eq40
    | exact resolve eq40 eq3837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3837
  have eq4859 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4848
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4848
    | exact resolve eq4848 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4848
  have eq4863 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4859
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4859
    | exact resolve eq4859 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859
  have eq6039 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (k (σ y) (σ y)) = (k (σ y) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3756 eq692
    | exact resolve eq692 eq3756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6080 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3756 eq3530
    | exact resolve eq3530 eq3756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3530 eq3756
  have eq6095 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq6080
  have eq6127 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3813 eq6095
    | exact resolve eq6095 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6095
  have eq6156 : (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (k (σ y) (σ y)) = (k (σ y) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3813 eq6039
    | exact resolve eq6039 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6039
  have eq6192 : (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (k (σ x) (σ x)) = (k (σ x) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3813 eq6156
    | exact resolve eq6156 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6156
  have eq6211 : (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ x) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6127 eq6192
    | exact resolve eq6192 eq6127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6127 eq6192
  have eq6219 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq658 eq6211
    | exact resolve eq6211 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq6211
  have eq6221 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3813 eq6219
    | exact resolve eq6219 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6219
  have eq6222 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq631 (σ x)
       grind)
    | (have r₁ := eq6221
       have r₂ := eq631 (σ x)
       grind)
    | exact resolve eq6221 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6221
  have eq6498 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op X2 (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 y X2 X0
       have i₂ := eq1078 X0 X1
       grind)
    | (have i₁ := eq177 x y x X0
       have i₂ := eq1078 X0 X1
       grind)
    | exact superpose eq1078 eq177
    | exact resolve eq177 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq8816 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq1077 x X0 X1 x
       have i₂ := eq3813
       grind)
    | exact superpose eq3813 eq1077
    | exact resolve eq1077 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq10489 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (k x x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3776 eq915
    | exact resolve eq915 eq3776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq3776
  have eq10522 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (k x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10489
  have eq10566 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (k x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq637 eq10522
    | exact resolve eq10522 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq10522
  have eq10623 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (k x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq768 eq10566
    | exact resolve eq10566 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq10566
  have eq10624 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (k x x) := by grind
  clear eq10623
  have eq10656 : y = (k x x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3599 eq10624
    | exact resolve eq10624 eq3599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3599 eq10624
  have eq10689 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq10656
       grind)
    | exact superpose eq10656 eq40
    | exact resolve eq40 eq10656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10656
  have eq10704 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq10689
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10689
    | exact resolve eq10689 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10689
  have eq10710 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq10704
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10704
    | exact resolve eq10704 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10704
  have eq13139 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq178 y X0
       have i₂ := eq3244
       grind)
    | exact superpose eq3244 eq178
    | exact resolve eq178 eq3244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq3244
  have eq13354 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3650 eq188
    | exact resolve eq188 eq3650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3650
  have eq14126 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq3851 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq3851
       grind)
    | exact resolve eq13 eq3851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851
  have eq14142 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq14126 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14126
  have eq36534 : x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq14142 eq3849
    | exact resolve eq3849 eq14142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3849 eq14142
  have eq36613 : x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq36534
  have eq36741 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq36613 eq42
    | exact resolve eq42 eq36613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq36613
  have eq36753 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq36741
    | exact resolve eq36741 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36741
  have eq36755 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq36753
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36753
    | exact resolve eq36753 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36753
  have eq36762 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq36755 eq631
    | (have j0 := eq631 (σ (M.op x y))
       grind)
    | exact resolve eq631 eq36755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36763 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq36755 eq602
    | (have j0 := eq602 (σ (M.op x y)) (σ (M.op x y)) x x
       grind)
    | exact resolve eq602 eq36755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq36765 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1163 eq36763
    | (have j1 := eq1163 (σ (M.op x y)) x (σ (M.op x y)) x
       grind)
    | exact resolve eq36763 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163 eq36763
  have eq36769 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq36755 eq36765
    | exact resolve eq36765 eq36755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36765
  have eq39846 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3557 eq611
    | (have j0 := eq611 (σ (M.op x y)) x
       grind)
    | exact resolve eq611 eq3557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3557
  have eq39854 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq4863 eq611
    | (have j0 := eq611 (σ x) x
       grind)
    | exact resolve eq611 eq4863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4863
  have eq39859 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq10710 eq611
    | (have j0 := eq611 (σ x) x
       grind)
    | exact resolve eq611 eq10710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611 eq10710
  have eq39949 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1080 eq39859
    | (have j0 := eq39859 (σ x)
       grind)
    | exact resolve eq39859 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39859
  have eq39951 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1080 eq39854
    | (have j0 := eq39854 (σ x)
       grind)
    | exact resolve eq39854 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39854
  have eq39970 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39949 eq39951
    | exact resolve eq39951 eq39949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39949 eq39951
  have eq39971 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq39970
  have eq40139 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq39971 eq188
    | exact resolve eq188 eq39971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39971
  have eq40263 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq39846 eq176
    | exact resolve eq176 eq39846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39846
  have eq41552 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq36769 eq40139
    | exact resolve eq40139 eq36769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40139
  have eq41553 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq36769 eq13354
    | exact resolve eq13354 eq36769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13354
  have eq41624 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq41552
  have eq41658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq41553
       have r₂ := eq3639
       grind)
    | exact resolve eq41553 eq3639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3639 eq41553
  have eq41659 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq41624
       have r₂ := eq27
       grind)
    | exact resolve eq41624 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41624
  have eq41677 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq41658
       have r₂ := eq27
       grind)
    | exact resolve eq41658 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41658
  have eq41685 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq6222 eq41677
    | exact resolve eq41677 eq6222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6222 eq41677
  have eq41868 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq41685 eq36769
    | exact resolve eq36769 eq41685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36769 eq41685
  have eq41890 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq41868
  have eq41921 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq41659 eq41890
    | exact resolve eq41890 eq41659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41659 eq41890
  have eq41943 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq41921
       have r₂ := eq36762
       grind)
    | exact resolve eq41921 eq36762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36762 eq41921
  have eq41959 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq41943 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq41943
       grind)
    | exact resolve eq13 eq41943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41976 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq41959 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41959
  have eq42381 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq41976 eq41943
    | exact resolve eq41943 eq41976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41943 eq41976
  have eq42438 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq42381
  have eq42482 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq36755 eq42438
    | exact resolve eq42438 eq36755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36755 eq42438
  have eq42533 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq42482 eq32
    | exact resolve eq32 eq42482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42482
  have eq42676 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq30 eq42533
    | exact resolve eq42533 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42533
  have eq42677 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq42676
  have eq42866 : (M.op x y) = (τ (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq42677 eq29
    | exact resolve eq29 eq42677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42677
  have eq42915 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq42866
    | exact resolve eq42866 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42866
  have eq42923 : (M.op x y) = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq42915 eq29
    | exact resolve eq29 eq42915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq42940 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq42915 eq3717
    | exact resolve eq3717 eq42915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3717
  have eq43005 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq42940
       have r₂ := eq3595
       grind)
    | exact resolve eq42940 eq3595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42940
  have eq43022 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq42923
    | exact resolve eq42923 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42923
  have eq43027 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq43022
       grind)
    | exact superpose eq43022 eq18
    | exact resolve eq18 eq43022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43022
  have eq43261 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq43027 eq13139
    | exact resolve eq13139 eq43027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13139 eq43027
  have eq43298 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq43261
       have r₂ := eq3595
       grind)
    | exact resolve eq43261 eq3595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43261
  have eq43305 : x = y ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2677 eq43298
    | exact resolve eq43298 eq2677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43298
  have eq43308 : x = (k y (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq43305
       have r₂ := eq3595
       grind)
    | exact resolve eq43305 eq3595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43305
  have eq44454 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43005 eq142
    | exact resolve eq142 eq43005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq43005
  have eq44500 : x = (k x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq44454
    | exact resolve eq44454 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44454
  have eq44510 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq631 x
       grind)
    | (have r₁ := eq44500
       have r₂ := eq631 x
       grind)
    | exact resolve eq44500 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44500
  have eq44523 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3813
       have i₂ := eq44510
       grind)
    | exact superpose eq44510 eq3813
    | exact resolve eq3813 eq44510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44566 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8816 X0 x
       have i₂ := eq44510
       grind)
    | exact superpose eq44510 eq8816
    | exact resolve eq8816 eq44510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44584 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq44510
       grind)
    | exact superpose eq44510 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq44510
       grind)
    | exact resolve eq13 eq44510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44590 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 x x x
       have i₂ := eq44510
       grind)
    | exact superpose eq44510 eq181
    | exact resolve eq181 eq44510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44601 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq44584 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44584
  have eq44619 : ∀ X0 : G, (k X0 x) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq44601 eq44566
    | exact resolve eq44566 eq44601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44566
  have eq44637 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42915 eq44523
    | exact resolve eq44523 eq42915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42915 eq44523
  have eq44638 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq44637
  have eq44667 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq44638 eq32
    | exact resolve eq32 eq44638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44638
  have eq44813 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq44667
    | exact resolve eq44667 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44667
  have eq44814 : y = (M.op x y) ∨ x = y := by grind
  clear eq44813
  have eq44841 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq44814
       grind)
    | exact superpose eq44814 eq18
    | exact resolve eq18 eq44814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44842 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq44814
       grind)
    | exact superpose eq44814 eq24
    | exact resolve eq24 eq44814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44874 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3595
       have i₂ := eq44814
       grind)
    | exact superpose eq44814 eq3595
    | (have r₁ := eq3595
       have r₂ := eq44814
       grind)
    | exact resolve eq3595 eq44814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44954 : x ≠ (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq44874
       have r₂ := eq3595
       grind)
    | exact resolve eq44874 eq3595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44874
  have eq44970 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq44842
    | exact resolve eq44842 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44842
  have eq45054 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq44841 eq2704
    | exact resolve eq2704 eq44841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2704 eq44841
  have eq45111 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq45054 X0
       grind)
    | (have r₁ := eq45054 X0
       have r₂ := eq3595
       grind)
    | exact resolve eq45054 eq3595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3595 eq45054
  have eq45159 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44590 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq44590
    | (have j0 := eq44590 y
       grind)
    | exact resolve eq44590 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44590
  have eq46655 : ∀ X0 X1 : G, x = (M.op y (M.op X1 (k X0 x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq3835 X1 X0
       have i₂ := eq44601 X0
       grind)
    | exact superpose eq44601 eq3835
    | exact resolve eq3835 eq44601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3835
  have eq46656 : ∀ X0 : G, (M.op x y) = (M.op x (k X0 x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3856 X0
       have i₂ := eq44601 X0
       grind)
    | exact superpose eq44601 eq3856
    | exact resolve eq3856 eq44601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3856
  have eq46670 : ∀ X0 X1 : G, (M.op X1 (k X0 x)) = (M.op X1 y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq8816 X1 X0
       have i₂ := eq44601 X0
       grind)
    | exact superpose eq44601 eq8816
    | exact resolve eq8816 eq44601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8816
  have eq46744 : x = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44510
       have i₂ := eq44601 x
       grind)
    | exact superpose eq44601 eq44510
    | exact resolve eq44510 eq44601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44510
  have eq46794 : x = (k (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45159
       have i₂ := eq44601 sF0
       grind)
    | exact superpose eq44601 eq45159
    | exact resolve eq45159 eq44601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45159
  have eq46795 : (M.op x y) = (M.op (k (M.op x y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq189 x
       have i₂ := eq44601 sF0
       grind)
    | exact superpose eq44601 eq189
    | exact resolve eq189 eq44601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq46840 : x = (k (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq46794
  have eq46842 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq46744
  have eq46874 : (M.op x y) = (M.op (k (M.op x y) x) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44814 eq46795
    | exact resolve eq46795 eq44814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44814 eq46795
  have eq46928 : ∀ X0 X1 : G, (k X1 x) = (M.op X1 (k X0 x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq44619 eq46670
    | exact resolve eq46670 eq44619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44619 eq46670
  have eq46938 : ∀ X0 : G, (M.op x y) = (M.op x (k X0 x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq44970 eq46656
    | (have j0 := eq46656 X0
       grind)
    | exact resolve eq46656 eq44970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46656
  have eq46939 : ∀ X0 X1 : G, x = (M.op x (M.op X1 (k X0 x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq44970 eq46655
    | exact resolve eq46655 eq44970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46655
  have eq46964 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq46840 eq46874
    | exact resolve eq46874 eq46840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46840 eq46874
  have eq46987 : ∀ X0 X1 : G, (k X1 x) = (M.op X1 (k X0 x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq44970 eq46928
    | (have j0 := eq46928 X0 X1
       grind)
    | exact resolve eq46928 eq44970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46928
  have eq46992 : ∀ X0 X1 : G, x = (M.op x (M.op X1 (k X0 x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq44970 eq46939
    | (have j0 := eq46939 X0 X1
       grind)
    | exact resolve eq46939 eq44970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44970 eq46939
  have eq47009 : ∀ X1 : G, x = (M.op x (k X1 x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq46987 eq46992
    | exact resolve eq46992 eq46987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46987 eq46992
  have eq47017 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46938 eq47009
    | exact resolve eq47009 eq46938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46938 eq47009
  have eq47018 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq47017
  have eq47066 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq46842
       grind)
    | exact superpose eq46842 eq40
    | exact resolve eq40 eq46842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46842
  have eq47119 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq47066
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47066
    | exact resolve eq47066 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47066
  have eq47139 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3813
       have i₂ := eq46964
       grind)
    | exact superpose eq46964 eq3813
    | exact resolve eq3813 eq46964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3813
  have eq47211 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44601 x
       have i₂ := eq46964
       grind)
    | exact superpose eq46964 eq44601
    | exact resolve eq44601 eq46964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44601 eq46964
  have eq47233 : (M.op x y) = (k x x) ∨ y = (M.op x y) := by grind
  clear eq47211
  have eq47245 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq47139
  have eq47592 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq47119 eq632
    | (have j0 := eq632 (σ x) X0
       grind)
    | (have r₁ := eq632 (σ x) x
       have r₂ := eq47119
       grind)
    | exact resolve eq632 eq47119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq47593 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47119 eq631
    | (have j0 := eq631 (σ x)
       grind)
    | (have r₁ := eq631 (σ x)
       have r₂ := eq47119
       grind)
    | exact resolve eq631 eq47119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq47596 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq47593
  have eq47597 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq47592 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47592
  have eq47686 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq47233
       grind)
    | exact superpose eq47233 eq40
    | exact resolve eq40 eq47233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq47233
  have eq47768 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq47686
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47686
    | exact resolve eq47686 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47686
  have eq47781 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq47768
    | exact resolve eq47768 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47768
  have eq47784 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47119 eq47781
    | exact resolve eq47781 eq47119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47119 eq47781
  have eq48099 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq47596 eq181
    | exact resolve eq181 eq47596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq51820 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47597 eq196
    | exact resolve eq196 eq47597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq52364 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq48099
    | (have j0 := eq48099 (σ y)
       grind)
    | exact resolve eq48099 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48099
  have eq52566 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52364 eq47597
    | exact resolve eq47597 eq52364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47597 eq52364
  have eq52585 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq52566
  have eq52957 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47245 eq51820
    | exact resolve eq51820 eq47245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47245 eq51820
  have eq52991 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq52957
  have eq53002 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq47784 eq52991
    | exact resolve eq52991 eq47784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52991
  have eq53009 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq52585 eq53002
    | exact resolve eq53002 eq52585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52585 eq53002
  have eq53013 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq47596 eq53009
    | exact resolve eq53009 eq47596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53009
  have eq53014 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq53013 eq27
    | exact resolve eq27 eq53013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53013
  have eq53149 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq53014
       have r₂ := eq47784
       grind)
    | exact resolve eq53014 eq47784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53014
  have eq53155 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53149 eq26
    | exact resolve eq26 eq53149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53149
  have eq53294 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47596 eq53155
    | exact resolve eq53155 eq47596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47596 eq53155
  have eq53305 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53294 eq27
    | exact resolve eq27 eq53294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53294
  have eq53434 : y = (M.op x y) := by
    first
    | (have r₁ := eq53305
       have r₂ := eq47784
       grind)
    | exact resolve eq53305 eq47784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47784 eq53305
  have eq53445 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq53434
       grind)
    | exact superpose eq53434 eq18
    | exact resolve eq18 eq53434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq53446 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq53434
       grind)
    | exact superpose eq53434 eq24
    | exact resolve eq24 eq53434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq53447 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq53434
       grind)
    | exact superpose eq53434 eq37
    | exact resolve eq37 eq53434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq53448 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq53434
       grind)
    | exact superpose eq53434 eq41
    | exact resolve eq41 eq53434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq53453 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq621
       have i₂ := eq53434
       grind)
    | exact superpose eq53434 eq621
    | exact resolve eq621 eq53434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq53459 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x y))) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1078 X0 X1
       have i₂ := eq53434
       grind)
    | exact superpose eq53434 eq1078
    | exact resolve eq1078 eq53434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq53577 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq53446 eq20
    | exact resolve eq20 eq53446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53580 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq53446 eq15
    | exact resolve eq15 eq53446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54131 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) x)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3535 eq53448
    | exact resolve eq53448 eq3535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3535 eq53448
  have eq54242 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) x)) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq54131
       have r₂ := eq44954
       grind)
    | exact resolve eq54131 eq44954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54131
  have eq54264 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) x)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq54242
    | exact resolve eq54242 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54242
  have eq54271 : (σ y) = (k (σ (M.op (M.op x y) x)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq53577 eq54264
    | exact resolve eq54264 eq53577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54264
  have eq54275 : (σ y) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq45111 eq54271
    | exact resolve eq54271 eq45111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45111 eq54271
  have eq54277 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2677 eq54275
    | exact resolve eq54275 eq2677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2677 eq54275
  have eq54279 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq54277
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq54277
    | exact resolve eq54277 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54277
  have eq54380 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op (M.op X0 (M.op x y)) (M.op x y))) ∨ (M.op (M.op X0 (M.op x y)) (M.op x y)) = (k (M.op X0 (M.op x y)) (M.op (M.op X0 (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq53459 eq692
    | exact resolve eq692 eq53459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq54382 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) ≠ (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ (M.op X1 (M.op X0 (M.op x y))) = (k X1 (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq53459 eq13
    | (have j0 := eq13 X1 (M.op X0 (M.op x y))
       grind)
    | exact resolve eq13 eq53459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54541 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (k X1 (M.op X0 (M.op x y))) ∨ (M.op X0 (M.op x y)) ≠ (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq53459 eq54382
    | (have j0 := eq54382 X0 X1
       grind)
    | exact resolve eq54382 eq53459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54382
  have eq54542 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op x y)) ∨ (M.op (M.op X0 (M.op x y)) (M.op x y)) = (k (M.op X0 (M.op x y)) (M.op (M.op X0 (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq53459 eq54380
    | (have j0 := eq54380 X0
       grind)
    | exact resolve eq54380 eq53459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53459 eq54380
  have eq54571 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = (k (M.op X0 (M.op x y)) (M.op (M.op X0 (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq54542 X0
       have j1 := eq54541 (M.op X0 (M.op x y)) (M.op X0 (M.op x y))
       grind)
    | (have r₁ := eq54542 X0
       have r₂ := eq54541 (M.op X0 (M.op x y)) x
       grind)
    | exact resolve eq54542 eq54541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54541 eq54542
  have eq56841 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq54279 eq626
    | exact resolve eq626 eq54279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56843 : (τ (σ y)) = (k x (τ (σ y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq54279 eq91
    | exact resolve eq91 eq54279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq54279
  have eq56857 : y = (k x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq32 eq56843
    | exact resolve eq56843 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56843
  have eq56864 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq56857
       have i₂ := eq53434
       grind)
    | exact superpose eq53434 eq56857
    | exact resolve eq56857 eq53434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56857
  have eq56870 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53453 eq56864
    | exact resolve eq56864 eq53453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53453 eq56864
  have eq56877 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56870 eq36
    | exact resolve eq36 eq56870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq56870
  have eq56901 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq56877
    | exact resolve eq56877 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56877
  have eq56904 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53577 eq56901
    | exact resolve eq56901 eq53577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56901
  have eq56917 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56904 eq626
    | exact resolve eq626 eq56904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq56904
  have eq58905 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq56917 eq176
    | exact resolve eq176 eq56917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq58934 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56917 eq28
    | exact resolve eq28 eq56917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56917
  have eq58966 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1080 eq58905
    | (have j0 := eq58905 (σ x)
       grind)
    | exact resolve eq58905 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58905
  have eq59012 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq58966 eq188
    | exact resolve eq188 eq58966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq74788 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40263 eq59012
    | exact resolve eq59012 eq40263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40263
  have eq74889 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq74788
       have r₂ := eq44954
       grind)
    | exact resolve eq74788 eq44954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74788
  have eq74903 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq53577 eq74889
    | exact resolve eq74889 eq53577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74889
  have eq74915 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq56841 eq74903
    | exact resolve eq74903 eq56841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74903
  have eq74916 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq74915
  have eq74964 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq74916 eq1080
    | exact resolve eq1080 eq74916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080 eq74916
  have eq90457 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58934 eq98
    | exact resolve eq98 eq58934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq58934
  have eq90540 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq90457
    | exact resolve eq90457 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq90457
  have eq90543 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90540
       have i₂ := eq53434
       grind)
    | exact superpose eq53434 eq90540
    | exact resolve eq90540 eq53434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90540
  have eq104918 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq53445 eq54571
    | exact resolve eq54571 eq53445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53445 eq54571
  have eq105181 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq104918 eq53447
    | exact resolve eq53447 eq104918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53447 eq104918
  have eq108963 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq74964 eq58966
    | exact resolve eq58966 eq74964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58966 eq74964
  have eq108976 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq108963
  have eq109025 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq108976
       have r₂ := eq44954
       grind)
    | exact resolve eq108976 eq44954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108976
  have eq109169 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq109025 eq59012
    | exact resolve eq59012 eq109025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59012 eq109025
  have eq109201 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq109169
  have eq109223 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq109201
       have r₂ := eq44954
       grind)
    | exact resolve eq109201 eq44954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109201
  have eq109233 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq56841 eq109223
    | exact resolve eq109223 eq56841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56841 eq109223
  have eq109234 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq109233
  have eq109338 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq109234
       grind)
    | exact superpose eq109234 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq109234
       grind)
    | exact resolve eq13 eq109234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109364 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq109338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109338
  have eq110018 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109234
       have i₂ := eq109364 x
       grind)
    | exact superpose eq109364 eq109234
    | exact resolve eq109234 eq109364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109234 eq109364
  have eq110173 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq110018
  have eq110329 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90543
       have i₂ := eq110173
       grind)
    | exact superpose eq110173 eq90543
    | exact resolve eq90543 eq110173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90543 eq110173
  have eq110384 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq110329
  have eq110947 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq110384 eq27
    | exact resolve eq27 eq110384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110384
  have eq111159 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq110947
       have r₂ := eq47018
       grind)
    | exact resolve eq110947 eq47018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47018 eq110947
  have eq111349 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq111159 eq53580
    | exact resolve eq53580 eq111159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53580 eq111159
  have eq111427 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq111349
    | exact resolve eq111349 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq111349
  have eq111428 : x = (M.op x y) := by grind
  clear eq111427
  have eq111692 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq43308 eq1041
    | (have j0 := eq1041 y (M.op x y) x x
       grind)
    | exact resolve eq1041 eq43308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041 eq43308
  have eq112240 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 x))) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq111692 X0 X1
       grind)
    | (have r₁ := eq111692 X0 X1
       have r₂ := eq44954
       grind)
    | exact resolve eq111692 eq44954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44954 eq111692
  have eq112336 : ∀ X0 X1 : G, (M.op x y) = (M.op y (M.op X0 (M.op X1 (M.op x y)))) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq112240 X0 X1
       have i₂ := eq111428
       grind)
    | exact superpose eq111428 eq112240
    | exact resolve eq112240 eq111428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112240
  have eq112391 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6498 eq112336
    | exact resolve eq112336 eq6498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6498 eq112336
  have eq112392 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq112391
  have eq112422 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq112392
       have i₂ := eq53434
       grind)
    | exact superpose eq53434 eq112392
    | exact resolve eq112392 eq53434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53434 eq112392
  have eq112443 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq112422
       have i₂ := eq111428
       grind)
    | exact superpose eq111428 eq112422
    | exact resolve eq112422 eq111428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112422
  have eq112444 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq112443
  have eq112959 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq111428
       grind)
    | exact superpose eq111428 eq22
    | exact resolve eq22 eq111428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq111428
  have eq113327 : (σ x) = (σ y) := by
    first
    | exact superpose eq112959 eq53446
    | exact resolve eq53446 eq112959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53446
  have eq113328 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq112959 eq20
    | exact resolve eq20 eq112959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112959
  have eq113492 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq113327 eq26
    | exact resolve eq26 eq113327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq113985 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq112444 eq105181
    | exact resolve eq105181 eq112444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105181 eq112444
  have eq114132 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq113985
    | exact resolve eq113985 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq113985
  have eq114152 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq53577 eq114132
    | exact resolve eq114132 eq53577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53577 eq114132
  have eq114160 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq113327 eq114152
    | exact resolve eq114152 eq113327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113327 eq114152
  have eq114553 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq113492 eq28
    | exact resolve eq28 eq113492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq113492
  have eq114591 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq114160 eq114553
    | exact resolve eq114553 eq114160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114160 eq114553
  have eq114592 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq114591
  have eq114644 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq114592 eq27
    | exact resolve eq27 eq114592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq114592
  have eq114814 : False := by grind
  exact eq114814

/-- `Equation1480`: `x = (y ◇ x) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation1480 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1480.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq85 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq180 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq85 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq85 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq85 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq13 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq195 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq196 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq195 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq200 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq196 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq196
    | (have j0 := eq196 X0 X1
       grind)
    | exact resolve eq196 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq201 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq200 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq594 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq201 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq201
    | exact resolve eq201 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq201 x y
       grind)
    | exact superpose eq201 eq16
    | (have j1 := eq201 x y
       grind)
    | exact resolve eq16 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq630 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq594 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq594
    | (have j0 := eq594 X0 X1
       grind)
    | exact resolve eq594 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq594
  have eq635 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq630 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq630
    | exact resolve eq630 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq722 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq635 (τ X1) X0
       grind)
    | exact superpose eq635 eq18
    | (have j1 := eq635 (τ X1) X0
       grind)
    | exact resolve eq18 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq635
  have eq939 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq722 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq722
    | exact resolve eq722 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq990 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq939 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq939
    | (have j0 := eq939 X0 X1
       grind)
    | exact resolve eq939 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq1075 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq608
       have i₂ := eq990 y x
       grind)
    | exact superpose eq990 eq608
    | (have j1 := eq990 (σ y) (σ x)
       grind)
    | (have r₁ := eq608
       have r₂ := eq990 y x
       grind)
    | exact resolve eq608 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1076 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1075
  have eq1128 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1076
  have eq1144 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq608
       have i₂ := eq1128
       grind)
    | exact superpose eq1128 eq608
    | exact resolve eq608 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq1128
  have eq1145 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1144
  have eq1146 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1145
  have eq1206 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1146
  have eq1224 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1206
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1206
    | exact resolve eq1206 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1229 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1224
       grind)
    | exact superpose eq1224 eq16
    | exact resolve eq16 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1297 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1229
       have i₂ := eq990 y x
       grind)
    | exact superpose eq990 eq1229
    | (have j1 := eq990 y x
       grind)
    | (have r₁ := eq1229
       have r₂ := eq990 y x
       grind)
    | exact resolve eq1229 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1298 : y = (M.op x x) := by grind
  clear eq1297
  have eq1302 : (M.op x y) = (k y x) := by grind
  clear eq1298
  have eq1369 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1229
       have i₂ := eq1302
       grind)
    | exact superpose eq1302 eq1229
    | exact resolve eq1229 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229 eq1302
  have eq1372 : False := by grind
  exact eq1372
