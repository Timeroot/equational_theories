import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyy_pxx_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
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
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X1 X0) X2) X1 X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : (σ (M.op x x)) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq39 (M.op x x)
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq39
    | exact resolve eq39 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq178 sF2
       grind)
    | exact superpose eq178 eq141
    | exact resolve eq141 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq691 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq718 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq750 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq719 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq719
    | (have j0 := eq719 (σ X0)
       grind)
    | exact resolve eq719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq1748 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1762 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 x X0 X1 y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1770 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1774 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1770 X0 x x X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1770
    | exact resolve eq1770 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770
  have eq1779 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1748 X0 x x X3 X4
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1748
    | exact resolve eq1748 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748
  have eq5475 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq691
       grind)
    | exact superpose eq691 eq39
    | exact resolve eq39 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq5476 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5475
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5475
    | exact resolve eq5475 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5475
  have eq5479 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq5476
    | exact resolve eq5476 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5476
  have eq15599 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0 X0 x X0
       have i₂ := eq1779 X0 X0 x
       grind)
    | exact superpose eq1779 eq176
    | exact resolve eq176 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15635 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1779 X0 X0 X0
       have i₂ := eq15599 X0
       grind)
    | exact superpose eq15599 eq1779
    | exact resolve eq1779 eq15599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15599
  have eq15729 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq178 (M.op X0 X0)
       have i₂ := eq15635 X0
       grind)
    | exact superpose eq15635 eq178
    | exact resolve eq178 eq15635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq15738 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1779 (M.op X0 X0) (M.op X0 X0) x
       have i₂ := eq15635 X0
       grind)
    | exact superpose eq15635 eq1779
    | exact resolve eq1779 eq15635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq15741 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15738 X0 X1
       have i₂ := eq177 X0 X0 X1
       grind)
    | exact superpose eq177 eq15738
    | exact resolve eq15738 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq15738
  have eq16726 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq1762 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq15741 X0 x
       grind)
    | exact superpose eq15741 eq1762
    | exact resolve eq1762 eq15741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1762
  have eq16732 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X1 (M.op X0 X0) (M.op X0 X0) X2
       have i₂ := eq15741 X0 X1
       grind)
    | exact superpose eq15741 eq176
    | exact resolve eq176 eq15741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq16733 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq15741 X0 X1
       grind)
    | exact superpose eq15741 eq16
    | exact resolve eq16 eq15741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16752 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16733 X0 X1
       have i₂ := eq15635 X0
       grind)
    | exact superpose eq15635 eq16733
    | exact resolve eq16733 eq15635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16733
  have eq16753 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16732 X0 X1 X2
       have i₂ := eq15635 X0
       grind)
    | exact superpose eq15635 eq16732
    | exact resolve eq16732 eq15635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16732
  have eq16757 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq16726 X0
       have i₂ := eq15635 X0
       grind)
    | exact superpose eq15635 eq16726
    | exact resolve eq16726 eq15635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15635 eq16726
  have eq16760 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X1) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq16753 x X1 X2
       have i₂ := eq16752 x (M.op X1 X2)
       grind)
    | exact superpose eq16752 eq16753
    | exact resolve eq16753 eq16752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16753
  have eq16763 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq16757 x
       have i₂ := eq16752 x sF0
       grind)
    | exact superpose eq16752 eq16757
    | exact resolve eq16757 eq16752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16757
  have eq16828 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15741 X1 X0
       have i₂ := eq16752 X1 X0
       grind)
    | exact superpose eq16752 eq15741
    | exact resolve eq15741 eq16752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15741
  have eq18172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5479 eq705
    | exact resolve eq705 eq5479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18181 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq18172
       have r₂ := eq27
       grind)
    | exact resolve eq18172 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18172
  have eq18192 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18181 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq18181
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq18181
       grind)
    | exact resolve eq12 eq18181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18204 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18181 eq16760
    | exact resolve eq16760 eq18181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18181
  have eq18208 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq18192
  have eq18209 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq18208
  have eq18219 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18204 eq18209
    | exact resolve eq18209 eq18204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18209
  have eq18228 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5479 eq18219
    | exact resolve eq18219 eq5479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5479 eq18219
  have eq18232 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18228 eq224
    | exact resolve eq224 eq18228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq18228
  have eq18285 : y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq18232
    | exact resolve eq18232 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18232
  have eq18286 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq691 eq18285
    | exact resolve eq18285 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq18285
  have eq18347 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16760 y x
       have i₂ := eq18286
       grind)
    | exact superpose eq18286 eq16760
    | exact resolve eq16760 eq18286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18286
  have eq18457 : ∀ X0 : G, y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16752 y X0
       have i₂ := eq18347
       grind)
    | exact superpose eq18347 eq16752
    | exact resolve eq16752 eq18347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16752 eq18347
  have eq19480 : ∀ X0 : G, y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1774 x x
       have i₂ := eq18457 X0
       grind)
    | exact superpose eq18457 eq1774
    | (have j1 := eq18457 X0
       grind)
    | exact resolve eq1774 eq18457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18457
  have eq19489 : ∀ X0 : G, y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19480 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19480
    | (have j0 := eq19480 X0
       grind)
    | exact resolve eq19480 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19480
  have eq19490 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19489 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19489
  have eq19534 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16760 y X0
       have i₂ := eq19490 X0
       grind)
    | exact superpose eq19490 eq16760
    | exact resolve eq16760 eq19490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16760 eq19490
  have eq19747 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq19534 x
       grind)
    | exact superpose eq19534 eq18
    | (have j1 := eq19534 x
       grind)
    | exact resolve eq18 eq19534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19534
  have eq19785 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq19747
  have eq19813 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19785 eq28
    | exact resolve eq28 eq19785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq19785
  have eq19908 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq19813
    | exact resolve eq19813 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq19813
  have eq19909 : y = (M.op x y) := by grind
  clear eq19908
  have eq19921 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq19909
       grind)
    | exact superpose eq19909 eq24
    | exact resolve eq24 eq19909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq19960 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19921 eq20
    | exact resolve eq20 eq19921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156561 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq18204 eq16828
    | exact resolve eq16828 eq18204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18204
  have eq156642 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq156561 X0
       have i₂ := eq19909
       grind)
    | exact superpose eq19909 eq156561
    | (have j0 := eq156561 X0
       grind)
    | exact resolve eq156561 eq19909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156561
  have eq156671 : ∀ X0 : G, x = (M.op x y) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq16763 eq156642
    | (have j0 := eq156642 X0
       grind)
    | exact resolve eq156642 eq16763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156642
  have eq156698 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq156671 X0
       have i₂ := eq19909
       grind)
    | exact superpose eq19909 eq156671
    | (have j0 := eq156671 X0
       grind)
    | exact resolve eq156671 eq19909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19909 eq156671
  have eq156795 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq156698 eq1774
    | (have j1 := eq156698 (σ x)
       grind)
    | exact resolve eq1774 eq156698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774 eq156698
  have eq156817 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq26 eq156795
    | (have j0 := eq156795 X0
       grind)
    | exact resolve eq156795 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156795
  have eq156967 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq156817 eq26
    | (have j1 := eq156817 (σ x)
       grind)
    | exact resolve eq26 eq156817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156817
  have eq157004 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq156967
  have eq157059 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15729 x
       have i₂ := eq157004
       grind)
    | exact superpose eq157004 eq15729
    | exact resolve eq15729 eq157004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15729 eq157004
  have eq157182 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq157059 eq750
    | (have j0 := eq750 (M.op x y)
       grind)
    | exact resolve eq750 eq157059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750 eq157059
  have eq157204 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq157182
  have eq157208 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq157204
    | exact resolve eq157204 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157204
  have eq157231 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19960 eq157208
    | exact resolve eq157208 eq19960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157208
  have eq158058 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq157231 eq16828
    | exact resolve eq16828 eq157231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16828 eq157231
  have eq158556 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq158058 eq26
    | (have j1 := eq158058 (σ x)
       grind)
    | exact resolve eq26 eq158058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158058
  have eq158593 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq158556
  have eq158612 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq158593 eq27
    | exact resolve eq27 eq158593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158593
  have eq158642 : x = (M.op x y) := by
    first
    | (have r₁ := eq158612
       have r₂ := eq19960
       grind)
    | exact resolve eq158612 eq19960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158612
  have eq158645 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq158642
       grind)
    | exact superpose eq158642 eq22
    | exact resolve eq22 eq158642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq158650 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq185
       have i₂ := eq158642
       grind)
    | exact superpose eq158642 eq185
    | exact resolve eq185 eq158642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq158685 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq16763
       have i₂ := eq158642
       grind)
    | exact superpose eq158642 eq16763
    | exact resolve eq16763 eq158642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16763 eq158642
  have eq158853 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq158685 eq158650
    | exact resolve eq158650 eq158685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158650 eq158685
  have eq158861 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq158853
    | exact resolve eq158853 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158853
  have eq158864 : (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq19960 eq158861
    | exact resolve eq158861 eq19960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19960 eq158861
  have eq158871 : (σ x) = (σ y) := by
    first
    | exact superpose eq158645 eq19921
    | exact resolve eq19921 eq158645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19921
  have eq158872 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq158645 eq20
    | exact resolve eq20 eq158645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq158645
  have eq159680 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq158871 eq26
    | exact resolve eq26 eq158871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq161050 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq158864 eq705
    | exact resolve eq705 eq158864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq158864
  have eq161102 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq158871 eq161050
    | exact resolve eq161050 eq158871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161050
  have eq161128 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq158871 eq161102
    | exact resolve eq161102 eq158871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161102
  have eq161144 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq159680 eq161128
    | exact resolve eq161128 eq159680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161128
  have eq161145 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq161144
  have eq161157 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq159680 eq161145
    | exact resolve eq161145 eq159680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159680 eq161145
  have eq161164 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq158871 eq161157
    | exact resolve eq161157 eq158871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158871 eq161157
  have eq161165 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq161164
  have eq161174 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq161165 eq27
    | exact resolve eq27 eq161165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq161165
  have eq161216 : False := by grind
  exact eq161216

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxx_x_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq29 : x = (τ (σ x)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq44 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44
    | (have j0 := eq44 y
       grind)
    | exact resolve eq44 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq132 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op y X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq179 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179
    | (have j0 := eq179 X0
       grind)
    | exact resolve eq179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq183 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 : G, (M.op (M.op X0 (k (M.op X0 X0) X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 (M.op X0 X0)
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op x (M.op (M.op x y) X0)) y) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X1 : G, (M.op y X1) = (M.op y (M.op y X1)) := by
    intro X1
    first
    | exact superpose eq174 eq550
    | exact resolve eq550 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq557 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ y) (M.op (σ y) X1)) := by
    intro X1
    first
    | exact superpose eq175 eq557
    | exact resolve eq557 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq808 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by
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
  have eq811 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq825 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (k X0 X1) X2)) X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq865 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq866 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq865 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq877 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq866 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq866
    | (have j0 := eq866 (σ X0)
       grind)
    | exact resolve eq866 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq880 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq825
       grind)
    | exact superpose eq825 eq40
    | exact resolve eq40 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq880
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq880
    | exact resolve eq880 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq883 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq881
    | exact resolve eq881 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq891 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq883 eq826
    | exact resolve eq826 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq891
       have r₂ := eq27
       grind)
    | exact resolve eq891 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq903 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq898 eq559
    | exact resolve eq559 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : (σ y) = (M.op (M.op (σ y) (k (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq898 eq543
    | exact resolve eq543 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq906 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq898 eq178
    | exact resolve eq178 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq913 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq883 eq906
    | exact resolve eq906 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq914 : (σ y) = (M.op (M.op (σ y) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq883 eq905
    | exact resolve eq905 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq920 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) X0)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq903 eq16
    | exact resolve eq16 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) (σ (M.op x y))) (M.op (σ y) X0)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq914 eq16
    | exact resolve eq16 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq1014 : (σ x) = (M.op (M.op (σ y) (σ (M.op x y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq913 eq920
    | exact resolve eq920 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913 eq920
  have eq1025 : (σ x) = (M.op (M.op (σ y) (σ (M.op x y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1014
  have eq1163 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1200 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 x X0 X1 y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1209 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1217 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1221 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1217 X0 x x X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1217
    | exact resolve eq1217 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1236 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1163 X0 x x X3 X4
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1163
    | exact resolve eq1163 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1827 : (σ y) = (M.op (M.op (M.op (σ y) (σ (M.op x y))) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq903 eq935
    | exact resolve eq935 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq935
  have eq1840 : (σ y) = (M.op (M.op (M.op (σ y) (σ (M.op x y))) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1827
  have eq1845 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1025 eq1840
    | exact resolve eq1840 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025 eq1840
  have eq1848 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq1845
    | exact resolve eq1845 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845
  have eq1849 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1848
  have eq1853 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq552 y
       have i₂ := eq1849
       grind)
    | exact superpose eq1849 eq552
    | exact resolve eq552 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq1863 : ∀ X0 : G, y = (M.op (M.op y (M.op x X0)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 y y X0
       have i₂ := eq1849
       grind)
    | exact superpose eq1849 eq16
    | exact resolve eq16 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1874 : ∀ X0 : G, x = (M.op (M.op y (M.op x X0)) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq1853
       grind)
    | exact superpose eq1853 eq16
    | exact resolve eq16 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1931 : y = (M.op (M.op y (M.op x y)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1863 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1863
    | (have j0 := eq1863 y
       grind)
    | exact resolve eq1863 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863
  have eq1953 : (M.op x y) = (M.op (M.op y y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1931 eq16
    | exact resolve eq16 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1958 : ∀ X0 : G, y = (M.op (M.op (M.op y (M.op x y)) (M.op y X0)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1931 eq16
    | exact resolve eq16 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931
  have eq1961 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1849 eq1953
    | exact resolve eq1953 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1849 eq1953
  have eq1974 : x = (M.op (M.op y (M.op x y)) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1961 eq1874
    | (have j0 := eq1874 y
       grind)
    | exact resolve eq1874 eq1961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874 eq1961
  have eq1987 : x = (M.op (M.op y (M.op x y)) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1974
  have eq2385 : y = (M.op (M.op (M.op y (M.op x y)) x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1958 x
       have i₂ := eq1853
       grind)
    | exact superpose eq1853 eq1958
    | exact resolve eq1958 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853 eq1958
  have eq2401 : y = (M.op (M.op (M.op y (M.op x y)) x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2385
  have eq2408 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1987 eq2401
    | exact resolve eq2401 eq1987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1987 eq2401
  have eq2411 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2408
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2408
    | exact resolve eq2408 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2408
  have eq2412 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2411
  have eq2419 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2412 eq811
    | (have r₁ := eq811
       have r₂ := eq2412
       grind)
    | exact resolve eq811 eq2412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq2420 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2419
  have eq2455 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2420 eq152
    | exact resolve eq152 eq2420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2420
  have eq2466 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2455
    | exact resolve eq2455 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2455
  have eq2474 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2466 eq559
    | exact resolve eq559 eq2466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq2477 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2466 eq178
    | exact resolve eq178 eq2466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2500 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) X0)) (σ x)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2474 eq16
    | exact resolve eq16 eq2474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2474
  have eq2885 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2500
    | (have j0 := eq2500 (σ y)
       grind)
    | exact resolve eq2500 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2500
  have eq2918 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2412 eq2885
    | exact resolve eq2885 eq2412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412 eq2885
  have eq2921 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2466 eq2918
    | exact resolve eq2918 eq2466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466 eq2918
  have eq2929 : (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2921 eq2477
    | exact resolve eq2477 eq2921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477 eq2921
  have eq2951 : (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq2929
  have eq2978 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2951 eq152
    | exact resolve eq152 eq2951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq2951
  have eq2985 : x = (k x y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2978
    | exact resolve eq2978 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2978
  have eq2986 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq2985
  have eq2993 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq825
       have i₂ := eq2986
       grind)
    | exact superpose eq2986 eq825
    | exact resolve eq825 eq2986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq3000 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq2986
       grind)
    | exact superpose eq2986 eq40
    | exact resolve eq40 eq2986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3001 : ∀ X0 : G, y = (M.op (M.op x (M.op x X0)) y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq831 x y X0
       have i₂ := eq2986
       grind)
    | exact superpose eq2986 eq831
    | (have j0 := eq831 x y x
       grind)
    | exact resolve eq831 eq2986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq3008 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2993
  have eq3012 : ∀ X0 : G, y = (M.op (M.op x X0) y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3001 X0
       have i₂ := eq1221 x X0
       grind)
    | (have i₁ := eq3001 X0
       have i₂ := eq1221 x (M.op x X0)
       grind)
    | exact superpose eq1221 eq3001
    | exact resolve eq3001 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3001
  have eq3013 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3000
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3000
    | exact resolve eq3000 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3000
  have eq3016 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op (M.op x X0) y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3012 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3012
    | (have j0 := eq3012 X0
       grind)
    | exact resolve eq3012 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3012
  have eq3017 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op (M.op x X0) y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq3016 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016
  have eq3019 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq3008 eq3017
    | exact resolve eq3017 eq3008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3017
  have eq3326 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3013 eq883
    | exact resolve eq883 eq3013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883 eq3013
  have eq3335 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3326
  have eq3348 : y = (M.op (M.op y (k x y)) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq543 y
       have i₂ := eq3008
       grind)
    | exact superpose eq3008 eq543
    | exact resolve eq543 eq3008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3360 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1221 y y
       have i₂ := eq3008
       grind)
    | exact superpose eq3008 eq1221
    | exact resolve eq1221 eq3008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3008
  have eq3365 : y = (M.op (M.op y x) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2986 eq3348
    | exact resolve eq3348 eq2986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3348
  have eq3367 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3360 eq3365
    | exact resolve eq3365 eq3360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3360 eq3365
  have eq3368 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3367
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3367
    | exact resolve eq3367 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3367
  have eq3369 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3368
  have eq3371 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3369
       grind)
    | exact superpose eq3369 eq24
    | exact resolve eq24 eq3369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3377 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq808
       have i₂ := eq3369
       grind)
    | exact superpose eq3369 eq808
    | (have r₁ := eq808
       have r₂ := eq3369
       grind)
    | exact resolve eq808 eq3369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq3378 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3377
  have eq3381 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3371
    | exact resolve eq3371 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371
  have eq3437 : (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq3335
       grind)
    | exact superpose eq3335 eq178
    | exact resolve eq178 eq3335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3335
  have eq3461 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2986 eq3437
    | exact resolve eq3437 eq2986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3437
  have eq3471 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3369 eq3461
    | exact resolve eq3461 eq3369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3461
  have eq3572 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) x) (M.op (M.op x y) X2)) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1200 eq176
    | exact resolve eq176 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq3585 : ∀ X2 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X2)) (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq3572 x x X2
       have i₂ := eq16 x x x
       grind)
    | exact superpose eq16 eq3572
    | exact resolve eq3572 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3572
  have eq3629 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq3471 eq16
    | exact resolve eq16 eq3471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3644 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq181 eq3629
    | exact resolve eq3629 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3629
  have eq3962 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3378 eq41
    | exact resolve eq41 eq3378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq3378
  have eq3968 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3962
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3962
    | exact resolve eq3962 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3962
  have eq3970 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3381 eq3968
    | exact resolve eq3968 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3968
  have eq3985 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq3644 eq16
    | exact resolve eq16 eq3644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3644
  have eq4001 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq3471 eq3985
    | exact resolve eq3985 eq3471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3471 eq3985
  have eq4010 : ∀ X0 : G, y = (M.op (M.op x X0) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq4001 eq174
    | exact resolve eq174 eq4001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4054 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq3369 eq4010
    | exact resolve eq4010 eq3369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4010
  have eq4058 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq4001 eq4054
    | exact resolve eq4054 eq4001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4001 eq4054
  have eq4296 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4058 x
       grind)
    | exact superpose eq4058 eq18
    | (have j1 := eq4058 x
       grind)
    | exact resolve eq18 eq4058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4058
  have eq4356 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq4296
  have eq4381 : (k (M.op x y) y) = (τ (k (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4356 eq132
    | exact resolve eq132 eq4356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq4356
  have eq4435 : (k x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq98 eq4381
    | exact resolve eq4381 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq4381
  have eq4446 : x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2986 eq4435
    | exact resolve eq4435 eq2986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986 eq4435
  have eq4448 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3369 eq4446
    | exact resolve eq4446 eq3369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4446
  have eq4485 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3970 eq826
    | exact resolve eq826 eq3970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4819 : x = (M.op (M.op (M.op (M.op x y) y) (M.op x y)) x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3019 eq1200
    | exact resolve eq1200 eq3019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4825 : ∀ X0 : G, (M.op (M.op (M.op x y) y) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq3019 eq16
    | exact resolve eq16 eq3019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4850 : ∀ X0 : G, (M.op (M.op (M.op x y) y) X0) = X0 ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq3369 eq4825
    | (have j0 := eq4825 X0
       grind)
    | exact resolve eq4825 eq3369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4825
  have eq4856 : (M.op x y) = (M.op (M.op (M.op (M.op x y) y) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3369 eq4819
    | exact resolve eq4819 eq3369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4819
  have eq4861 : (M.op x y) = (M.op (M.op (M.op (M.op x y) y) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq3369 eq4856
    | exact resolve eq4856 eq3369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4856
  have eq4863 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq4850 eq4861
    | exact resolve eq4861 eq4850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4850 eq4861
  have eq4901 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq4863 eq3019
    | exact resolve eq3019 eq4863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4918 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq4901
  have eq4926 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq3369 eq4918
    | exact resolve eq4918 eq3369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4918
  have eq4927 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq4926
  have eq4955 : ∀ X0 : G, y = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq180 X0 y
       have i₂ := eq4927
       grind)
    | exact superpose eq4927 eq180
    | exact resolve eq180 eq4927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq4927
  have eq4986 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq3585 eq4955
    | exact resolve eq4955 eq3585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3585 eq4955
  have eq4987 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq4986
  have eq4996 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4987 eq3019
    | exact resolve eq3019 eq4987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3019 eq4987
  have eq5012 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq4996
  have eq5015 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3369 eq5012
    | exact resolve eq5012 eq3369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5012
  have eq5192 : (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq5015
       grind)
    | exact superpose eq5015 eq178
    | exact resolve eq178 eq5015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5015
  have eq5223 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4448 eq5192
    | exact resolve eq5192 eq4448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4448 eq5192
  have eq5228 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4863 eq5223
    | exact resolve eq5223 eq4863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4863 eq5223
  have eq5229 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq5228
  have eq5246 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5229 eq16
    | exact resolve eq16 eq5229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5265 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq181 eq5246
    | exact resolve eq5246 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq5246
  have eq5419 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5265 eq16
    | exact resolve eq16 eq5265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5265
  have eq5444 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5229 eq5419
    | exact resolve eq5419 eq5229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5229 eq5419
  have eq5567 : ∀ X0 : G, y = (M.op (M.op x X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5444 eq174
    | exact resolve eq174 eq5444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq5624 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3369 eq5567
    | exact resolve eq5567 eq3369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3369 eq5567
  have eq5630 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5444 eq5624
    | exact resolve eq5624 eq5444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5444 eq5624
  have eq5831 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5630 x
       grind)
    | exact superpose eq5630 eq18
    | (have j1 := eq5630 x
       grind)
    | exact resolve eq18 eq5630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5630
  have eq5903 : y = (M.op x y) := by grind
  clear eq5831
  have eq5920 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5903
       grind)
    | exact superpose eq5903 eq24
    | exact resolve eq24 eq5903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq5922 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq5903
       grind)
    | exact superpose eq5903 eq40
    | exact resolve eq40 eq5903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5903
  have eq5931 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5920 eq20
    | exact resolve eq20 eq5920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63928 : (σ y) = (M.op (M.op (σ y) (k (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4485 eq543
    | exact resolve eq543 eq4485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq63940 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4485 eq1221
    | exact resolve eq1221 eq4485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4485
  have eq63955 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3970 eq63928
    | exact resolve eq63928 eq3970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3970 eq63928
  have eq63960 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq63940 eq63955
    | exact resolve eq63955 eq63940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63940 eq63955
  have eq63963 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq63960
    | exact resolve eq63960 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63960
  have eq63964 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq63963
  have eq64030 : (k x (M.op x y)) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq63964 eq178
    | exact resolve eq178 eq63964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64042 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq63964 eq1236
    | exact resolve eq1236 eq63964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65821 : x = (M.op (M.op (M.op x y) (M.op x y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64042 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq64042
    | (have j0 := eq64042 y
       grind)
    | exact resolve eq64042 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq64042
  have eq65880 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq63964 eq65821
    | exact resolve eq65821 eq63964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63964 eq65821
  have eq65886 : x = (k x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64030
       have i₂ := eq65880
       grind)
    | exact superpose eq65880 eq64030
    | exact resolve eq64030 eq65880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65903 : (k x x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq178 x
       have i₂ := eq65880
       grind)
    | exact superpose eq65880 eq178
    | exact resolve eq178 eq65880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65880
  have eq65939 : x = (k x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq65886
  have eq65954 : (k x x) = (k x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64030 eq65903
    | exact resolve eq65903 eq64030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64030 eq65903
  have eq65959 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq65939 eq65954
    | exact resolve eq65954 eq65939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65954
  have eq65980 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq65939 eq5922
    | exact resolve eq5922 eq65939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5922 eq65939
  have eq65990 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65980
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq65980
    | exact resolve eq65980 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65980
  have eq66029 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq877 x
       have i₂ := eq65959
       grind)
    | exact superpose eq65959 eq877
    | (have j0 := eq877 x
       grind)
    | exact resolve eq877 eq65959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq65959
  have eq66038 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq66029
  have eq66045 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66038
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq66038
    | exact resolve eq66038 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66038
  have eq66110 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq66045 eq1236
    | exact resolve eq1236 eq66045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236 eq66045
  have eq66131 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq66110 X0
       have i₂ := eq1221 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq66110 x
       have i₂ := eq1221 sF2 x
       grind)
    | exact superpose eq1221 eq66110
    | exact resolve eq66110 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66110
  have eq66197 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq65990 eq826
    | exact resolve eq826 eq65990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826 eq65990
  have eq66225 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq66197
  have eq66259 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq66225 eq183
    | exact resolve eq183 eq66225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq66225
  have eq66307 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66131 eq66259
    | exact resolve eq66259 eq66131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66131 eq66259
  have eq66310 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq66307
    | exact resolve eq66307 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66307
  have eq66311 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq66310
  have eq66314 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66311 eq27
    | exact resolve eq27 eq66311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66311
  have eq66323 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq66314
       have r₂ := eq3381
       grind)
    | exact resolve eq66314 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381 eq66314
  have eq66326 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66323 eq27
    | exact resolve eq27 eq66323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66327 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq66323 eq175
    | exact resolve eq175 eq66323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq66338 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq66323 eq1209
    | exact resolve eq1209 eq66323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq66341 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66338 x x
       have i₂ := eq16 sF2 x x
       grind)
    | exact superpose eq16 eq66338
    | exact resolve eq66338 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66338
  have eq66345 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq66327 X0
       have i₂ := eq1221 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq66327 x
       have i₂ := eq1221 sF2 x
       grind)
    | exact superpose eq1221 eq66327
    | exact resolve eq66327 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221 eq66327
  have eq66346 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5931 eq66326
    | exact resolve eq66326 eq5931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66326
  have eq66590 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66341 eq66345
    | exact resolve eq66345 eq66341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66341 eq66345
  have eq66649 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq66590
  have eq66660 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq66649
    | exact resolve eq66649 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66649
  have eq66670 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66323 eq66660
    | exact resolve eq66660 eq66323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66323 eq66660
  have eq66675 : x = (M.op x y) := by
    first
    | (have r₁ := eq66670
       have r₂ := eq66346
       grind)
    | exact resolve eq66670 eq66346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66346 eq66670
  have eq66679 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq66675
       grind)
    | exact superpose eq66675 eq22
    | exact resolve eq22 eq66675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq66687 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op x y)) X1)) (M.op x y)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1200 X0 X1
       have i₂ := eq66675
       grind)
    | exact superpose eq66675 eq1200
    | exact resolve eq1200 eq66675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200 eq66675
  have eq66810 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq66687 x x
       have i₂ := eq16 sF0 x x
       grind)
    | exact superpose eq16 eq66687
    | exact resolve eq66687 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66687
  have eq66821 : (σ x) = (σ y) := by
    first
    | exact superpose eq66679 eq5920
    | exact resolve eq5920 eq66679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5920
  have eq66822 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq66679 eq20
    | exact resolve eq20 eq66679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66679
  have eq67427 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq66821 eq26
    | exact resolve eq26 eq66821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq68381 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq66810 eq178
    | exact resolve eq178 eq66810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq68410 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq66810 eq68381
    | exact resolve eq68381 eq66810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66810 eq68381
  have eq68443 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq68410 eq37
    | exact resolve eq37 eq68410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq68410
  have eq68464 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq68443
    | exact resolve eq68443 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq68443
  have eq68484 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq5931 eq68464
    | exact resolve eq68464 eq5931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5931 eq68464
  have eq68503 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq66821 eq68484
    | exact resolve eq68484 eq66821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66821 eq68484
  have eq68593 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq67427 eq11
    | exact resolve eq11 eq67427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67427
  have eq68616 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq68593
  have eq68622 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq68503 eq68616
    | exact resolve eq68616 eq68503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68503 eq68616
  have eq68623 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq68622
  have eq68628 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq68623 eq27
    | exact resolve eq27 eq68623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq68623
  have eq68649 : False := by grind
  exact eq68649

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
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
  have eq75 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X1 (M.op (M.op X1 X0) X2))) = X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X1 (M.op (M.op X1 X0) X2))) = X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq75 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  clear eq70
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq110
    | exact resolve eq110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq111
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq111
    | exact resolve eq111 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq129 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq23 eq38
  have eq474 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq474 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq474
    | exact resolve eq474 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq778 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    grind
  clear eq76
  have eq779 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq778 X0 X1 X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq778
    | (have j0 := eq778 X0 X1 X2
       grind)
    | exact resolve eq778 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq780 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq779 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq817 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X2 (M.op (M.op X2 X0) X3)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq780 (M.op X0 X1) (M.op X2 (M.op (M.op X2 X0) X3)) X0
       have i₂ := eq53 X0 X2 X3 X1
       grind)
    | exact superpose eq53 eq780
    | exact resolve eq780 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq780
  have eq836 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq817 X0 X1 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq817
    | exact resolve eq817 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq916 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq836 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq836
    | (have j0 := eq836 x y
       grind)
    | exact resolve eq836 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq919 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq836
    | (have j0 := eq836 (σ x) (σ y)
       grind)
    | exact resolve eq836 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq933 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq916 eq129
    | exact resolve eq129 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq916
  have eq937 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq21 eq933
    | exact resolve eq933 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq944 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq937 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq945 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq944
  have eq1058 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq945 eq478
    | exact resolve eq478 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq1061 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1058
  have eq15910 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15911 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15910
    | exact resolve eq15910 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15910
  have eq15922 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15911
       have r₂ := eq28
       grind)
    | exact resolve eq15911 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15911
  have eq15925 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15922
    | exact resolve eq15922 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15922
  have eq15958 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15925 eq478
    | exact resolve eq478 eq15925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15925
  have eq15967 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15958
    | exact resolve eq15958 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15958
  have eq15968 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15967
  have eq15998 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq478 x x
       have i₂ := eq15968
       grind)
    | exact superpose eq15968 eq478
    | exact resolve eq478 eq15968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15968
  have eq16007 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15998
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15998
    | exact resolve eq15998 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15998
  have eq16008 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16007
  have eq16011 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16008 eq28
    | exact resolve eq28 eq16008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16027 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16008 eq919
    | exact resolve eq919 eq16008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919 eq16008
  have eq16045 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16027 eq112
    | exact resolve eq112 eq16027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq16027
  have eq16060 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq16045
  have eq16070 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16060
       have r₂ := eq16011
       grind)
    | exact resolve eq16060 eq16011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16011 eq16060
  have eq16104 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq478 x x
       have i₂ := eq16070
       grind)
    | exact superpose eq16070 eq478
    | exact resolve eq478 eq16070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq16070
  have eq16113 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16104
    | exact resolve eq16104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq16104
  have eq16114 : y = (M.op x y) := by grind
  clear eq16113
  have eq16119 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq16114 eq21
    | exact resolve eq21 eq16114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16114
  have eq16235 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq16119
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16119
    | exact resolve eq16119 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16119
  have eq16237 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq16235 eq27
    | exact resolve eq27 eq16235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq16235
  have eq16356 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1061 eq16237
    | exact resolve eq16237 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061 eq16237
  have eq16366 : False := by grind
  exact eq16366

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxx_pyy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq29 : x = (τ (σ x)) := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 : G, (M.op (M.op X0 (k (M.op X0 X0) X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 (M.op X0 X0)
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq559 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ y) (M.op (σ y) X1)) := by
    intro X1
    first
    | exact superpose eq175 eq557
    | exact resolve eq557 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq808 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq811 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq808
       grind)
    | exact superpose eq808 eq39
    | exact resolve eq39 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq890 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq889
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq889
    | exact resolve eq889 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq892 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq890
    | exact resolve eq890 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq900 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq892 eq811
    | exact resolve eq811 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq907 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq900
       have r₂ := eq27
       grind)
    | exact resolve eq900 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq912 : (σ x) = (M.op (M.op (σ x) (k (σ y) (σ x))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq907 eq543
    | exact resolve eq543 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq913 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq907 eq178
    | exact resolve eq178 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq892 eq913
    | exact resolve eq913 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq921 : (σ x) = (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq892 eq912
    | exact resolve eq912 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892 eq912
  have eq923 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq920 eq559
    | exact resolve eq559 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ (M.op x y))) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq921 eq16
    | exact resolve eq16 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1193 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 x X0 X1 y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1199 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1208 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1212 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1208 X0 x x X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1208
    | exact resolve eq1208 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1357 : (σ x) = (M.op (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq907 eq944
    | exact resolve eq944 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq1370 : (σ x) = (M.op (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1357
  have eq1413 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1370 eq176
    | exact resolve eq176 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1414 : (σ y) = (M.op (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1370 eq16
    | exact resolve eq16 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1421 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq921 eq1414
    | exact resolve eq1414 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq1422 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq921 eq1413
    | exact resolve eq1413 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq1413
  have eq1425 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1421
    | exact resolve eq1421 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421
  have eq1429 : (k y x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq178 x
       have i₂ := eq1425
       grind)
    | exact superpose eq1425 eq178
    | exact resolve eq178 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1586 : (σ y) = (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq923 eq1422
    | exact resolve eq1422 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq1599 : (σ y) = (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1586
  have eq1612 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1599 eq1370
    | exact resolve eq1370 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370 eq1599
  have eq1622 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1612
  have eq1631 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1622 eq1422
    | exact resolve eq1422 eq1622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422 eq1622
  have eq1642 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1631
  have eq1646 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq907 eq1642
    | exact resolve eq1642 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642
  have eq1654 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1646 eq920
    | exact resolve eq920 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1665 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1646 eq16
    | exact resolve eq16 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq1668 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1654
  have eq1671 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq559 eq1665
    | exact resolve eq1665 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq1665
  have eq1782 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) (σ y)) (M.op X0 X1)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq1671 eq176
    | exact resolve eq176 eq1671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1783 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1671 eq16
    | exact resolve eq16 eq1671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671
  have eq1795 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq920 eq1783
    | exact resolve eq1783 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq1796 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op X0 X1)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq920 eq1782
    | exact resolve eq1782 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq1782
  have eq1802 : ∀ X0 : G, y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1668 eq1795
    | exact resolve eq1795 eq1668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq1803 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op X0 X1)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq1668 eq1796
    | exact resolve eq1796 eq1668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668 eq1796
  have eq1805 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq1802 eq1803
    | exact resolve eq1803 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802 eq1803
  have eq1892 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1805 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1805
    | (have j0 := eq1805 x y
       grind)
    | exact resolve eq1805 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1915 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq1805 X0 X1
       grind)
    | exact superpose eq1805 eq16
    | exact resolve eq16 eq1805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805
  have eq2047 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq1915 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1915 eq178
    | exact resolve eq178 eq1915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915
  have eq2572 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq2047 sF2
       grind)
    | exact superpose eq2047 eq141
    | exact resolve eq141 eq2047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2047
  have eq2587 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq907 eq2572
    | exact resolve eq2572 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907 eq2572
  have eq2594 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq2587
    | exact resolve eq2587 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587
  have eq2597 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq808 eq2594
    | exact resolve eq2594 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq2594
  have eq5188 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1212 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1212
    | (have j0 := eq1212 x y
       grind)
    | exact resolve eq1212 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5193 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1212 x x
       have i₂ := eq2597
       grind)
    | exact superpose eq2597 eq1212
    | exact resolve eq1212 eq2597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2597
  have eq5279 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5193
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5193
    | exact resolve eq5193 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5193
  have eq5280 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5279
  have eq5286 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5280 eq175
    | exact resolve eq175 eq5280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5292 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5286 X0
       have i₂ := eq1212 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq5286 x
       have i₂ := eq1212 sF2 x
       grind)
    | exact superpose eq1212 eq5286
    | exact resolve eq5286 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5286
  have eq5293 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq5292
    | (have j0 := eq5292 (σ y)
       grind)
    | exact resolve eq5292 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5308 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq5292 eq176
    | exact resolve eq176 eq5292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5309 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5292 eq16
    | exact resolve eq16 eq5292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5292
  have eq5330 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq5309
    | (have j0 := eq5309 X0
       grind)
    | exact resolve eq5309 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5309
  have eq5331 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26 eq5308
    | (have j0 := eq5308 X0 X1
       grind)
    | exact resolve eq5308 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5308
  have eq5336 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5280 eq5293
    | exact resolve eq5293 eq5280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5293
  have eq5337 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5280 eq5330
    | exact resolve eq5330 eq5280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5330
  have eq5338 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 X1)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq5280 eq5331
    | exact resolve eq5331 eq5280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5331
  have eq5341 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq5336
    | exact resolve eq5336 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5336
  have eq5342 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq5337 eq5338
    | exact resolve eq5338 eq5337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5338
  have eq5345 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5280 eq5341
    | exact resolve eq5341 eq5280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5341
  have eq5354 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5345 eq31
    | exact resolve eq31 eq5345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq5345
  have eq5448 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq5354
    | exact resolve eq5354 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5354
  have eq5467 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1429
       have i₂ := eq5448
       grind)
    | exact superpose eq5448 eq1429
    | exact resolve eq1429 eq5448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429 eq5448
  have eq5541 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq5467
  have eq5618 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5280 eq5541
    | exact resolve eq5541 eq5280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5280 eq5541
  have eq5619 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5618
  have eq5724 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5337 eq178
    | exact resolve eq178 eq5337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5777 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5337 eq5724
    | exact resolve eq5724 eq5337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5337 eq5724
  have eq5821 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5777 eq141
    | exact resolve eq141 eq5777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq5777
  have eq5854 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq5821
    | exact resolve eq5821 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5821
  have eq6001 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq850 x x
       have i₂ := eq5854
       grind)
    | exact superpose eq5854 eq850
    | (have j0 := eq850 x x
       grind)
    | (have r₁ := eq850 x x
       have r₂ := eq5854
       grind)
    | exact resolve eq850 eq5854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq5854
  have eq6002 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6001
  have eq6003 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6002
  have eq6195 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq5342 X0 X1
       grind)
    | exact superpose eq5342 eq16
    | exact resolve eq16 eq5342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6989 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6195 x X0
       have i₂ := eq6003
       grind)
    | exact superpose eq6003 eq6195
    | exact resolve eq6195 eq6003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6003 eq6195
  have eq7060 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6989 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6989
  have eq7142 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7060 y
       grind)
    | exact superpose eq7060 eq18
    | (have j1 := eq7060 y
       grind)
    | exact resolve eq18 eq7060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7164 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5342 x X0
       have i₂ := eq7060 X0
       grind)
    | exact superpose eq7060 eq5342
    | (have j1 := eq7060 y
       grind)
    | exact resolve eq5342 eq7060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5342 eq7060
  have eq7174 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7164 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7164
  have eq7182 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq7142
  have eq7228 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq7182
       grind)
    | exact superpose eq7182 eq24
    | exact resolve eq24 eq7182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7231 : ∀ X0 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq7182
       grind)
    | exact superpose eq7182 eq174
    | exact resolve eq174 eq7182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7325 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq7228
    | exact resolve eq7228 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7228
  have eq7596 : ∀ X0 : G, x = (M.op (M.op (M.op x (M.op y X0)) (M.op x y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq1193 x X0
       have i₂ := eq1892
       grind)
    | exact superpose eq1892 eq1193
    | exact resolve eq1193 eq1892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892
  have eq7638 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) x) (M.op (M.op x y) X2)) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1193 eq176
    | exact resolve eq176 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq7656 : ∀ X2 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X2)) (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq7638 x x X2
       have i₂ := eq16 x x x
       grind)
    | exact superpose eq16 eq7638
    | exact resolve eq7638 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7638
  have eq7673 : ∀ X0 : G, x = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq7174 eq7596
    | (have j1 := eq7174 (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y))
       grind)
    | exact resolve eq7596 eq7174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7174 eq7596
  have eq7693 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq7656 eq7673
    | exact resolve eq7673 eq7656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7656 eq7673
  have eq7694 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7693
  have eq7816 : (M.op x y) = (M.op (M.op x x) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7694 eq7231
    | exact resolve eq7231 eq7694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7231 eq7694
  have eq7839 : (M.op x y) = (M.op (M.op x x) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7816
  have eq7916 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7839
       have i₂ := eq1425
       grind)
    | exact superpose eq1425 eq7839
    | exact resolve eq7839 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425 eq7839
  have eq7964 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7916
  have eq7980 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7182 eq7964
    | exact resolve eq7964 eq7182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7182 eq7964
  have eq9289 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5619 eq7980
    | exact resolve eq7980 eq5619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5619 eq7980
  have eq9338 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9289
  have eq9349 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9338 eq39
    | exact resolve eq39 eq9338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq9338
  have eq9352 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9349
    | exact resolve eq9349 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9349
  have eq9354 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7325 eq9352
    | exact resolve eq9352 eq7325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9352
  have eq9361 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9354 eq811
    | exact resolve eq811 eq9354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811 eq9354
  have eq9367 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9361
  have eq9413 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9367 eq1212
    | exact resolve eq1212 eq9367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9367
  have eq9437 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9413
    | exact resolve eq9413 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9413
  have eq9438 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9437
  have eq9442 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9438 eq27
    | exact resolve eq27 eq9438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9438
  have eq9467 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9442
       have r₂ := eq7325
       grind)
    | exact resolve eq9442 eq7325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9442
  have eq9469 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9467 eq27
    | exact resolve eq27 eq9467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9470 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9467 eq175
    | exact resolve eq175 eq9467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq9474 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq9467 eq1199
    | exact resolve eq1199 eq9467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq9477 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9474 x x
       have i₂ := eq16 sF2 x x
       grind)
    | exact superpose eq16 eq9474
    | exact resolve eq9474 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9474
  have eq9479 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9470 X0
       have i₂ := eq1212 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq9470 x
       have i₂ := eq1212 sF2 x
       grind)
    | exact superpose eq1212 eq9470
    | exact resolve eq9470 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212 eq9470
  have eq9480 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7325 eq9469
    | exact resolve eq9469 eq7325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7325 eq9469
  have eq9483 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq9480
  have eq9770 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9477 eq9479
    | exact resolve eq9479 eq9477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9477 eq9479
  have eq9824 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9770
  have eq9836 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9824
    | exact resolve eq9824 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9824
  have eq9844 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9467 eq9836
    | exact resolve eq9836 eq9467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9467 eq9836
  have eq9850 : x = (M.op x y) := by
    first
    | (have r₁ := eq9844
       have r₂ := eq9483
       grind)
    | exact resolve eq9844 eq9483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9483 eq9844
  have eq9854 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9850
       grind)
    | exact superpose eq9850 eq18
    | exact resolve eq18 eq9850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq9855 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq9850
       grind)
    | exact superpose eq9850 eq22
    | exact resolve eq22 eq9850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq9861 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op x y)) X1)) (M.op x y)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1193 X0 X1
       have i₂ := eq9850
       grind)
    | exact superpose eq9850 eq1193
    | exact resolve eq1193 eq9850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193 eq9850
  have eq9863 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq9861 x x
       have i₂ := eq16 sF0 x x
       grind)
    | exact superpose eq16 eq9861
    | exact resolve eq9861 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9861
  have eq9867 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9855 eq20
    | exact resolve eq20 eq9855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10011 : y = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq9854 eq174
    | exact resolve eq174 eq9854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq10032 : y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq5188 eq10011
    | exact resolve eq10011 eq5188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5188 eq10011
  have eq10038 : y = (M.op x y) := by
    first
    | exact superpose eq9854 eq10032
    | exact resolve eq10032 eq9854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9854 eq10032
  have eq10048 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq10038
       grind)
    | exact superpose eq10038 eq24
    | exact resolve eq24 eq10038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10038
  have eq10103 : (σ x) = (σ y) := by
    first
    | exact superpose eq9855 eq10048
    | exact resolve eq10048 eq9855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9855 eq10048
  have eq10105 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10103 eq26
    | exact resolve eq26 eq10103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq10103
  have eq10213 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq9863 eq178
    | exact resolve eq178 eq9863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq10239 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq9863 eq10213
    | exact resolve eq10213 eq9863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9863 eq10213
  have eq10244 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq10239 eq37
    | exact resolve eq37 eq10239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq10239
  have eq10255 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10244
    | exact resolve eq10244 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10244
  have eq10257 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq9867 eq10255
    | exact resolve eq10255 eq9867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10255
  have eq10333 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10105 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10105
  have eq10347 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10333
  have eq10353 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10257 eq10347
    | exact resolve eq10347 eq10257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10257 eq10347
  have eq10354 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10353
  have eq10358 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq10354 eq27
    | exact resolve eq27 eq10354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq10354
  have eq10369 : False := by grind
  exact eq10369

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pxx_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
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
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq93
    | exact resolve eq93 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq351 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq360 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq360
    | exact resolve eq360 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq366 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq351 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq351
    | exact resolve eq351 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq384 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq363 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq363
    | (have j0 := eq363 x y
       grind)
    | exact resolve eq363 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq363
    | (have j0 := eq363 (σ x) (σ y)
       grind)
    | exact resolve eq363 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq384 eq14
    | exact resolve eq14 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq73 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq73 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq73 X0 X0
       grind)
    | exact resolve eq12 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq593 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq586 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq595 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq593 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq593 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq593 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq593 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq604 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq595 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq595
    | (have j0 := eq595 X0 X1
       grind)
    | exact resolve eq595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq3255 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0 x X0
       have i₂ := eq366 X0 X0 x
       grind)
    | exact superpose eq366 eq53
    | exact resolve eq53 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3296 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq366 X0 X0 X0
       have i₂ := eq3255 X0
       grind)
    | exact superpose eq3255 eq366
    | exact resolve eq366 eq3255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq3255
  have eq3458 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq3471 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3458 X0
       have i₂ := eq3296 X0
       grind)
    | exact superpose eq3296 eq3458
    | exact resolve eq3458 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296 eq3458
  have eq13032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13033 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13032
    | exact resolve eq13032 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13032
  have eq13044 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq13033
       have r₂ := eq28
       grind)
    | exact resolve eq13033 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13033
  have eq13046 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13044
    | exact resolve eq13044 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13044
  have eq13054 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq13046
  have eq13074 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13054
    | exact resolve eq13054 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13054
  have eq16299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq13074 eq95
    | exact resolve eq95 eq13074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13074
  have eq16315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16299
  have eq16318 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16315
       have r₂ := eq28
       grind)
    | exact resolve eq16315 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16315
  have eq16327 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16318
  have eq16352 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16327
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16327
    | exact resolve eq16327 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16327
  have eq16790 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq16352
       grind)
    | exact superpose eq16352 eq70
    | exact resolve eq70 eq16352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq16352
  have eq16816 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq16790
    | exact resolve eq16790 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16790
  have eq17515 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16816 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq16816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17524 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq17515
    | exact resolve eq17515 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17515
  have eq17535 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17524
       have r₂ := eq28
       grind)
    | exact resolve eq17524 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17524
  have eq17537 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq17535
    | exact resolve eq17535 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17535
  have eq17538 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17537
  have eq17652 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17538
  have eq17680 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17652
    | exact resolve eq17652 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17652
  have eq17794 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17680 eq16816
    | exact resolve eq16816 eq17680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16816 eq17680
  have eq17802 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17794
  have eq17808 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17802
       have r₂ := eq28
       grind)
    | exact resolve eq17802 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17802
  have eq17813 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17808 eq52
    | exact resolve eq52 eq17808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq17822 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17808 eq386
    | exact resolve eq386 eq17808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17844 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17813 X0
       have i₂ := eq363 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq17813 x
       have i₂ := eq363 sF2 x
       grind)
    | exact superpose eq363 eq17813
    | exact resolve eq17813 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17813
  have eq18276 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17822 eq17844
    | exact resolve eq17844 eq17822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17822 eq17844
  have eq18334 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18276
  have eq18353 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq18334
    | exact resolve eq18334 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18334
  have eq18362 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18353 eq28
    | exact resolve eq28 eq18353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18385 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18353 eq17808
    | exact resolve eq17808 eq18353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17808
  have eq18388 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq18385
  have eq18397 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18388 eq27
    | exact resolve eq27 eq18388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18398 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18388 eq30
    | exact resolve eq30 eq18388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18388
  have eq18564 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq18398
    | exact resolve eq18398 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18398
  have eq19349 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq18397
  have eq19388 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq386 eq19349
    | exact resolve eq19349 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq19349
  have eq19761 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18353 eq19388
    | exact resolve eq19388 eq18353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18353 eq19388
  have eq19779 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq19761
  have eq20156 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19779 eq95
    | exact resolve eq95 eq19779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq19779
  have eq20178 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq20156
  have eq20191 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20178
       have r₂ := eq18362
       grind)
    | exact resolve eq20178 eq18362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18362 eq20178
  have eq21014 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq363 x x
       have i₂ := eq20191
       grind)
    | exact superpose eq20191 eq363
    | exact resolve eq363 eq20191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20191
  have eq21024 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21014
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21014
    | exact resolve eq21014 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21014
  have eq21100 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq21024
  have eq21102 : x = (M.op x y) := by
    first
    | (have r₁ := eq21100
       have r₂ := eq18564
       grind)
    | exact resolve eq21100 eq18564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18564 eq21100
  have eq21158 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21102 eq21
    | exact resolve eq21 eq21102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq21218 : x = (M.op x x) := by
    first
    | exact superpose eq21102 eq384
    | exact resolve eq384 eq21102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq21219 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | exact superpose eq21102 eq402
    | exact resolve eq402 eq21102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq21235 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq21219 X0
       have i₂ := eq363 x X0
       grind)
    | (have i₁ := eq21219 X0
       have i₂ := eq363 x (M.op x X0)
       grind)
    | exact superpose eq363 eq21219
    | exact resolve eq21219 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq21219
  have eq21291 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21158
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21158
    | exact resolve eq21158 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21158
  have eq21298 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21291 eq27
    | exact resolve eq27 eq21291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq21466 : x = (k x x) := by
    first
    | (have i₁ := eq3471 x
       have i₂ := eq21218
       grind)
    | exact superpose eq21218 eq3471
    | exact resolve eq3471 eq21218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3471
  have eq21614 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq604 x x
       have i₂ := eq21466
       grind)
    | exact superpose eq21466 eq604
    | (have j0 := eq604 x x
       grind)
    | exact resolve eq604 eq21466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq21466
  have eq21617 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21614
  have eq21618 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21617
  have eq21631 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21618
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21618
    | exact resolve eq21618 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21618
  have eq21647 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21291 eq21631
    | exact resolve eq21631 eq21291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21631
  have eq21852 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq21235 X0
       grind)
    | exact superpose eq21235 eq14
    | exact resolve eq14 eq21235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21235
  have eq21914 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq21852 X0
       have i₂ := eq21218
       grind)
    | exact superpose eq21218 eq21852
    | exact resolve eq21852 eq21218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21218 eq21852
  have eq21947 : y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq21914 y
       grind)
    | exact superpose eq21914 eq19
    | (have j1 := eq21914 y
       grind)
    | exact resolve eq19 eq21914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21914
  have eq22049 : x = y := by
    first
    | exact superpose eq21102 eq21947
    | exact resolve eq21947 eq21102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21102 eq21947
  have eq22111 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq22049
       grind)
    | exact superpose eq22049 eq25
    | exact resolve eq25 eq22049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq22049
  have eq22238 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq22111
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22111
    | exact resolve eq22111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22111
  have eq22297 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21291 eq22238
    | exact resolve eq22238 eq21291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21291 eq22238
  have eq22534 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22297 eq21298
    | exact resolve eq21298 eq22297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21298 eq22297
  have eq22538 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21647 eq22534
    | exact resolve eq22534 eq21647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21647 eq22534
  have eq22603 : False := by grind
  exact eq22603

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pxy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
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
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq93
    | exact resolve eq93 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq351 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq360 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq360
    | exact resolve eq360 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq366 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq351 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq351
    | exact resolve eq351 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq384 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq363 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq363
    | (have j0 := eq363 x y
       grind)
    | exact resolve eq363 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq363
    | (have j0 := eq363 (σ x) (σ y)
       grind)
    | exact resolve eq363 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq384 eq14
    | exact resolve eq14 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq73 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq73 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq73 X0 X0
       grind)
    | exact resolve eq12 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq593 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq586 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq595 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq593 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq593 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq593 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq593 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq604 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq595 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq595
    | (have j0 := eq595 X0 X1
       grind)
    | exact resolve eq595 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq3261 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0 x X0
       have i₂ := eq366 X0 X0 x
       grind)
    | exact superpose eq366 eq53
    | exact resolve eq53 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3302 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq366 X0 X0 X0
       have i₂ := eq3261 X0
       grind)
    | exact superpose eq3261 eq366
    | exact resolve eq366 eq3261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq3261
  have eq3466 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq3479 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3466 X0
       have i₂ := eq3302 X0
       grind)
    | exact superpose eq3302 eq3466
    | exact resolve eq3466 eq3302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3302 eq3466
  have eq13125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13125
    | exact resolve eq13125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13125
  have eq13137 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq13126
       have r₂ := eq28
       grind)
    | exact resolve eq13126 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13126
  have eq13139 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13137
    | exact resolve eq13137 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13137
  have eq13147 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq13139
  have eq13168 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq13147
    | exact resolve eq13147 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13147
  have eq16410 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq13168 eq95
    | exact resolve eq95 eq13168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13168
  have eq16426 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16410
  have eq16429 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16426
       have r₂ := eq28
       grind)
    | exact resolve eq16426 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16426
  have eq16438 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16429
  have eq16464 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16438
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16438
    | exact resolve eq16438 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16438
  have eq16907 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq16464
       grind)
    | exact superpose eq16464 eq70
    | exact resolve eq70 eq16464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq16464
  have eq16933 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq16907
    | exact resolve eq16907 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16907
  have eq17638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16933 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq16933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq17638
    | exact resolve eq17638 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17638
  have eq17658 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17647
       have r₂ := eq28
       grind)
    | exact resolve eq17647 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17647
  have eq17660 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq17658
    | exact resolve eq17658 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17658
  have eq17661 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17660
  have eq17779 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17661
  have eq17808 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17779
    | exact resolve eq17779 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17779
  have eq17923 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17808 eq16933
    | exact resolve eq16933 eq17808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16933 eq17808
  have eq17931 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17923
  have eq17937 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17931
       have r₂ := eq28
       grind)
    | exact resolve eq17931 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17931
  have eq17942 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17937 eq52
    | exact resolve eq52 eq17937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq17951 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17937 eq386
    | exact resolve eq386 eq17937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17973 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17942 X0
       have i₂ := eq363 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq17942 x
       have i₂ := eq363 sF2 x
       grind)
    | exact superpose eq363 eq17942
    | exact resolve eq17942 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17942
  have eq18416 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17951 eq17973
    | exact resolve eq17973 eq17951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17951 eq17973
  have eq18474 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18416
  have eq18493 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq18474
    | exact resolve eq18474 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18474
  have eq18502 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18493 eq28
    | exact resolve eq28 eq18493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18525 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18493 eq17937
    | exact resolve eq17937 eq18493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17937
  have eq18528 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq18525
  have eq18537 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18528 eq27
    | exact resolve eq27 eq18528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18538 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18528 eq30
    | exact resolve eq30 eq18528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18528
  have eq18704 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq18538
    | exact resolve eq18538 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18538
  have eq19494 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq18537
  have eq19534 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq386 eq19494
    | exact resolve eq19494 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq19494
  have eq19911 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18493 eq19534
    | exact resolve eq19534 eq18493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18493 eq19534
  have eq19929 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq19911
  have eq20312 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19929 eq95
    | exact resolve eq95 eq19929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq19929
  have eq20334 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq20312
  have eq20347 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20334
       have r₂ := eq18502
       grind)
    | exact resolve eq20334 eq18502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18502 eq20334
  have eq21179 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq363 x x
       have i₂ := eq20347
       grind)
    | exact superpose eq20347 eq363
    | exact resolve eq363 eq20347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20347
  have eq21189 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21179
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21179
    | exact resolve eq21179 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21179
  have eq21266 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq21189
  have eq21268 : x = (M.op x y) := by
    first
    | (have r₁ := eq21266
       have r₂ := eq18704
       grind)
    | exact resolve eq21266 eq18704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18704 eq21266
  have eq21324 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21268 eq21
    | exact resolve eq21 eq21268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq21384 : x = (M.op x x) := by
    first
    | exact superpose eq21268 eq384
    | exact resolve eq384 eq21268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq21385 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | exact superpose eq21268 eq402
    | exact resolve eq402 eq21268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq21401 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq21385 X0
       have i₂ := eq363 x X0
       grind)
    | (have i₁ := eq21385 X0
       have i₂ := eq363 x (M.op x X0)
       grind)
    | exact superpose eq363 eq21385
    | exact resolve eq21385 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq21385
  have eq21457 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21324
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21324
    | exact resolve eq21324 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21324
  have eq21464 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21457 eq27
    | exact resolve eq27 eq21457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq21632 : x = (k x x) := by
    first
    | (have i₁ := eq3479 x
       have i₂ := eq21384
       grind)
    | exact superpose eq21384 eq3479
    | exact resolve eq3479 eq21384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3479
  have eq21782 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq604 x x
       have i₂ := eq21632
       grind)
    | exact superpose eq21632 eq604
    | (have j0 := eq604 x x
       grind)
    | exact resolve eq604 eq21632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq21632
  have eq21785 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21782
  have eq21786 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21785
  have eq21799 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21786
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21786
    | exact resolve eq21786 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21786
  have eq21815 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21457 eq21799
    | exact resolve eq21799 eq21457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21799
  have eq22024 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq21401 X0
       grind)
    | exact superpose eq21401 eq14
    | exact resolve eq14 eq21401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21401
  have eq22083 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22024 X0
       have i₂ := eq21384
       grind)
    | exact superpose eq21384 eq22024
    | exact resolve eq22024 eq21384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21384 eq22024
  have eq22116 : y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq22083 y
       grind)
    | exact superpose eq22083 eq19
    | (have j1 := eq22083 y
       grind)
    | exact resolve eq19 eq22083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq22083
  have eq22218 : x = y := by
    first
    | exact superpose eq21268 eq22116
    | exact resolve eq22116 eq21268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21268 eq22116
  have eq22282 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq22218
       grind)
    | exact superpose eq22218 eq25
    | exact resolve eq25 eq22218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq22218
  have eq22409 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq22282
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22282
    | exact resolve eq22282 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22282
  have eq22468 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21457 eq22409
    | exact resolve eq22409 eq21457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21457 eq22409
  have eq22705 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22468 eq21464
    | exact resolve eq21464 eq22468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21464 eq22468
  have eq22709 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21815 eq22705
    | exact resolve eq22705 eq21815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21815 eq22705
  have eq22774 : False := by grind
  exact eq22774

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxx_pxx_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  clear eq36
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (M.op X0 (k (M.op X0 X0) X0)) X0) = X0 := by
    intro X0
    grind
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq91
    | exact resolve eq91 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq380 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op (M.op X0 X0) (M.op (k (M.op X0 X0) X0) X1)) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (k (M.op X0 X0) X0) X0 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq53
    | exact resolve eq53 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq381 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq394 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq394
    | exact resolve eq394 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq399 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq381 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq381
    | exact resolve eq381 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq407 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq396 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq396
    | (have j0 := eq396 x y
       grind)
    | exact resolve eq396 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq750 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq76 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq751 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq750 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq3259 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0 x X0
       have i₂ := eq399 X0 X0 x
       grind)
    | exact superpose eq399 eq53
    | exact resolve eq53 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3295 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq399 X0 X0 X0
       have i₂ := eq3259 X0
       grind)
    | exact superpose eq3259 eq399
    | exact resolve eq399 eq3259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq3259
  have eq3312 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  clear eq3295
  have eq3343 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq751 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq751
    | (have j0 := eq751 (τ X0)
       grind)
    | exact resolve eq751 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3351 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3343 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3343
    | (have j0 := eq3343 X0
       grind)
    | exact resolve eq3343 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3343
  have eq3357 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3351 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3351
    | (have j0 := eq3351 X0
       grind)
    | exact resolve eq3351 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3351
  have eq3361 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq3389 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3361 X0
       have i₂ := eq3312 X0
       grind)
    | exact superpose eq3312 eq3361
    | exact resolve eq3361 eq3312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3361
  have eq6004 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq3312 X0
       grind)
    | exact superpose eq3312 eq380
    | exact resolve eq380 eq3312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq6005 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6004 X0 X1
       have i₂ := eq396 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq6004 X0 X1
       have i₂ := eq396 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq396 eq6004
    | exact resolve eq6004 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq6004
  have eq6118 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq6005 X0 X1
       grind)
    | exact superpose eq6005 eq14
    | exact resolve eq14 eq6005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6137 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X0) X1) = X1 := by
    intro X0 X1
    grind
  clear eq6118
  have eq6153 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6137 X0 X1
       have i₂ := eq3312 X0
       grind)
    | exact superpose eq3312 eq6137
    | exact resolve eq6137 eq3312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6137
  have eq6174 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6005 X1 X0
       have i₂ := eq6153 X1 X0
       grind)
    | exact superpose eq6153 eq6005
    | exact resolve eq6005 eq6153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6005
  have eq6181 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X0
       have i₂ := eq6153 X1 X0
       grind)
    | exact superpose eq6153 eq14
    | exact resolve eq14 eq6153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq20401
    | exact resolve eq20401 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20401
  have eq20413 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq20402
       have r₂ := eq28
       grind)
    | exact resolve eq20402 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20402
  have eq20429 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20413 eq3312
    | exact resolve eq3312 eq20413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20413
  have eq20483 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20429 eq104
    | exact resolve eq104 eq20429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq20429
  have eq20519 : y = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq20483
    | exact resolve eq20483 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20483
  have eq20522 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq3357 y
       grind)
    | (have r₁ := eq20519
       have r₂ := eq3357 y
       grind)
    | exact resolve eq20519 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357 eq20519
  have eq20539 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20522 eq3312
    | exact resolve eq3312 eq20522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20568 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20522 eq6181
    | exact resolve eq6181 eq20522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20522
  have eq20570 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq20568
    | exact resolve eq20568 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20568
  have eq20594 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3312 y
       have i₂ := eq20570
       grind)
    | exact superpose eq20570 eq3312
    | exact resolve eq3312 eq20570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3312 eq20570
  have eq20660 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq751 y
       have i₂ := eq20594
       grind)
    | exact superpose eq20594 eq751
    | (have j0 := eq751 y
       grind)
    | exact resolve eq751 eq20594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20594
  have eq20669 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq20660
  have eq20675 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq20669
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20669
    | exact resolve eq20669 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20669
  have eq24284 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq20675 eq6174
    | exact resolve eq6174 eq20675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20675
  have eq27333 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24284 eq27
    | (have j1 := eq24284 (σ x)
       grind)
    | exact resolve eq27 eq24284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24284
  have eq27382 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq27333
  have eq27444 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3389 y
       have i₂ := eq27382
       grind)
    | exact superpose eq27382 eq3389
    | exact resolve eq3389 eq27382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3389 eq27382
  have eq27578 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq751 x
       have i₂ := eq27444
       grind)
    | exact superpose eq27444 eq751
    | (have j0 := eq751 x
       grind)
    | exact resolve eq751 eq27444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751 eq27444
  have eq27587 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq27578
  have eq27593 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27587
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27587
    | exact resolve eq27587 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27587
  have eq28134 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27593 eq6153
    | exact resolve eq6153 eq27593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27593
  have eq28598 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28134 eq27
    | (have j1 := eq28134 (σ y)
       grind)
    | exact resolve eq27 eq28134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28134
  have eq28677 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28598
  have eq28694 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq28677 eq28
    | exact resolve eq28 eq28677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq28677
  have eq133525 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20539 eq92
    | exact resolve eq92 eq20539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq20539
  have eq133537 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by grind
  clear eq133525
  have eq133579 : ∀ X0 : G, x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6153 y X0
       have i₂ := eq133537
       grind)
    | exact superpose eq133537 eq6153
    | exact resolve eq6153 eq133537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133537
  have eq133952 : ∀ X0 : G, y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6181 y y
       have i₂ := eq133579 X0
       grind)
    | exact superpose eq133579 eq6181
    | (have j1 := eq133579 X0
       grind)
    | exact resolve eq6181 eq133579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6181 eq133579
  have eq133989 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq133952 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq133952
    | (have j0 := eq133952 X0
       grind)
    | exact resolve eq133952 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133952
  have eq134055 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6174 X0 y
       have i₂ := eq133989 y
       grind)
    | exact superpose eq133989 eq6174
    | exact resolve eq6174 eq133989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6174 eq133989
  have eq135085 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq134055 x
       grind)
    | exact superpose eq134055 eq19
    | (have j1 := eq134055 x
       grind)
    | exact resolve eq19 eq134055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134055
  have eq135326 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq135085
  have eq135867 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq135326 eq29
    | exact resolve eq29 eq135326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq135326
  have eq136289 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq135867
    | exact resolve eq135867 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq135867
  have eq136297 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq136289 eq21
    | exact resolve eq21 eq136289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136289
  have eq136762 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136297
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq136297
    | exact resolve eq136297 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136297
  have eq136763 : x = (M.op x y) := by
    first
    | (have r₁ := eq136762
       have r₂ := eq28694
       grind)
    | exact resolve eq136762 eq28694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136762
  have eq137662 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq136763 eq21
    | exact resolve eq21 eq136763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq137722 : x = (M.op x x) := by
    first
    | exact superpose eq136763 eq407
    | exact resolve eq407 eq136763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq138233 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq137662
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq137662
    | exact resolve eq137662 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137662
  have eq138874 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6153 x X0
       have i₂ := eq137722
       grind)
    | exact superpose eq137722 eq6153
    | exact resolve eq6153 eq137722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6153 eq137722
  have eq143373 : y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq138874 y
       grind)
    | exact superpose eq138874 eq19
    | (have j1 := eq138874 y
       grind)
    | exact resolve eq19 eq138874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq138874
  have eq143725 : x = y := by
    first
    | exact superpose eq136763 eq143373
    | exact resolve eq143373 eq136763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136763 eq143373
  have eq145140 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq143725
       grind)
    | exact superpose eq143725 eq25
    | exact resolve eq25 eq143725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq143725
  have eq145474 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq145140
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq145140
    | exact resolve eq145140 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq145140
  have eq145605 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq138233 eq145474
    | exact resolve eq145474 eq138233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138233 eq145474
  have eq145660 : False := by grind
  exact eq145660

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_pxx_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  clear eq36
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq88
    | exact resolve eq88 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq101 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq344 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq353 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq353
    | exact resolve eq353 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq356 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq346
    | (have j0 := eq346 X0 X1
       grind)
    | exact resolve eq346 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq358 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq344 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq344
    | exact resolve eq344 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq457 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq458 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq457 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq2982 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq356 eq53
    | exact resolve eq53 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2992 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2982 eq356
    | exact resolve eq356 eq2982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq2982
  have eq3007 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2992 eq14
    | exact resolve eq14 eq2992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2992
  have eq3009 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq3007 X0
       have i₂ := eq355 (M.op sF4 sF4) (M.op (M.op sF4 sF4) X0)
       grind)
    | (have i₁ := eq3007 x
       have i₂ := eq355 (M.op sF4 sF4) x
       grind)
    | exact superpose eq355 eq3007
    | exact resolve eq3007 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq3007
  have eq3111 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0 x X0
       have i₂ := eq358 X0 X0 x
       grind)
    | exact superpose eq358 eq53
    | exact resolve eq53 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3146 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq358 X0 X0 X0
       have i₂ := eq3111 X0
       grind)
    | exact superpose eq3111 eq358
    | exact resolve eq358 eq3111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3147 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X0 X0 X1
       have i₂ := eq3111 X0
       grind)
    | exact superpose eq3111 eq53
    | exact resolve eq53 eq3111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq3111
  have eq3187 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq458 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq458
    | (have j0 := eq458 (τ X0)
       grind)
    | exact resolve eq458 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3195 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3187 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3187
    | (have j0 := eq3187 X0
       grind)
    | exact resolve eq3187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3187
  have eq3201 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3195 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3195
    | (have j0 := eq3195 X0
       grind)
    | exact resolve eq3195 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3195
  have eq3274 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq3286 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3274 X0
       have i₂ := eq3146 X0
       grind)
    | exact superpose eq3146 eq3274
    | exact resolve eq3274 eq3146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3274
  have eq15712 : (σ x) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq3009 eq348
    | exact resolve eq348 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq15713 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq3009 eq14
    | exact resolve eq14 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3009
  have eq15754 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15713 X0
       have i₂ := eq3146 sF4
       grind)
    | exact superpose eq3146 eq15713
    | exact resolve eq15713 eq3146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3146 eq15713
  have eq15755 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq15712
       have i₂ := eq3147 sF4 sF4
       grind)
    | exact superpose eq3147 eq15712
    | exact resolve eq15712 eq3147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3147 eq15712
  have eq15757 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq15755 eq52
    | exact resolve eq52 eq15755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq15755
  have eq16044 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) X1) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq15754 eq358
    | exact resolve eq358 eq15754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq16070 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq15754 eq16044
    | exact resolve eq16044 eq15754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15754 eq16044
  have eq16751 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X0
       have i₂ := eq16070 X0 X1
       grind)
    | exact superpose eq16070 eq14
    | exact resolve eq14 eq16070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19255 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19256 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq19255
    | exact resolve eq19255 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19255
  have eq19267 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq19256
       have r₂ := eq28
       grind)
    | exact resolve eq19256 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19256
  have eq19277 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19267 eq3286
    | exact resolve eq3286 eq19267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19267
  have eq19319 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19277 eq101
    | exact resolve eq101 eq19277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq19277
  have eq19358 : y = (k y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq19319
    | exact resolve eq19319 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19319
  have eq19361 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq3201 y
       grind)
    | (have r₁ := eq19358
       have r₂ := eq3201 y
       grind)
    | exact resolve eq19358 eq3201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3201 eq19358
  have eq19368 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  have eq19390 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19361 eq16070
    | exact resolve eq16070 eq19361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19361
  have eq19392 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq19390
    | exact resolve eq19390 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19390
  have eq19394 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq19368
    | exact resolve eq19368 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19368
  have eq19408 : ∀ X0 : G, x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16751 y X0
       have i₂ := eq19392
       grind)
    | exact superpose eq19392 eq16751
    | exact resolve eq16751 eq19392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19392
  have eq19505 : ∀ X0 : G, x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3286 y
       have i₂ := eq19408 X0
       grind)
    | exact superpose eq19408 eq3286
    | (have j1 := eq19408 X0
       grind)
    | exact resolve eq3286 eq19408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19408
  have eq23134 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq458 x
       have i₂ := eq19505 X0
       grind)
    | exact superpose eq19505 eq458
    | (have j0 := eq458 x
       have j1 := eq19505 X0
       grind)
    | exact resolve eq458 eq19505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19505
  have eq23143 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq23134 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23134
  have eq23149 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23143 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23143
    | (have j0 := eq23143 X0
       grind)
    | exact resolve eq23143 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq23143
  have eq24950 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15757
       have i₂ := eq23149 (M.op sF2 sF2)
       grind)
    | exact superpose eq23149 eq15757
    | (have j1 := eq23149 X0
       grind)
    | exact resolve eq15757 eq23149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15757 eq23149
  have eq25008 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq24950
    | (have j0 := eq24950 X0
       grind)
    | exact resolve eq24950 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24950
  have eq25009 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq25008 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25008
  have eq25040 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3286 y
       have i₂ := eq25009 y
       grind)
    | exact superpose eq25009 eq3286
    | exact resolve eq3286 eq25009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3286 eq25009
  have eq25138 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq458 y
       have i₂ := eq25040
       grind)
    | exact superpose eq25040 eq458
    | (have j0 := eq458 y
       grind)
    | exact resolve eq458 eq25040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458 eq25040
  have eq25147 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25138
  have eq25153 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25147
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq25147
    | exact resolve eq25147 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25147
  have eq25419 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq25153 eq16751
    | exact resolve eq16751 eq25153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25153
  have eq25756 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f25756_12 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
      intro X0 X1
      grind
    have f25756_13 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f25756_21 : (σ y) ≠ (M.op X0 (σ y)) := by grind
    have f25756_22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f25756_24 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
      intro X0
      first
      | (have j0 := f25756_13 X0
         grind)
      | (have r₁ := f25756_13 X0
         have r₂ := f25756_22
         grind)
      | exact resolve f25756_13 f25756_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f25756_25 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
      intro X0
      first
      | (have i₁ := f25756_12 (σ y) X0
         have i₂ := f25756_24 X0
         grind)
      | exact superpose f25756_24 f25756_12
      | exact resolve f25756_12 f25756_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f25756_29 : (σ y) ≠ (σ y) := by
      first
      | (have i₁ := f25756_21
         have i₂ := f25756_25 X0
         grind)
      | exact superpose f25756_25 f25756_21
      | (have r₁ := f25756_21
         have r₂ := f25756_25 X0
         grind)
      | exact resolve f25756_21 f25756_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f25756_30 : False := by grind
    exact f25756_30
  clear eq25419
  have eq25970 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25756 eq27
    | (have j1 := eq25756 (σ x)
       grind)
    | exact resolve eq27 eq25756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq25756
  have eq26010 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25970
  have eq26029 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq26010 eq28
    | exact resolve eq28 eq26010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq105939 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26010 eq19394
    | exact resolve eq19394 eq26010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19394 eq26010
  have eq106511 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq105939 eq89
    | exact resolve eq89 eq105939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq105939
  have eq106522 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq106511
  have eq106530 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq106522
       have r₂ := eq26029
       grind)
    | exact resolve eq106522 eq26029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106522
  have eq106559 : ∀ X0 : G, x = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16751 y X0
       have i₂ := eq106530
       grind)
    | exact superpose eq106530 eq16751
    | exact resolve eq16751 eq106530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16751 eq106530
  have eq106719 : ∀ X0 : G, y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16070 y y
       have i₂ := eq106559 X0
       grind)
    | exact superpose eq106559 eq16070
    | (have j1 := eq106559 X0
       grind)
    | exact resolve eq16070 eq106559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106559
  have eq106732 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq106719 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq106719
    | (have j0 := eq106719 X0
       grind)
    | exact resolve eq106719 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106719
  have eq107012 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16070 y X0
       have i₂ := eq106732 X0
       grind)
    | exact superpose eq106732 eq16070
    | exact resolve eq16070 eq106732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16070 eq106732
  have eq107248 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq107012 x
       grind)
    | exact superpose eq107012 eq19
    | (have j1 := eq107012 x
       grind)
    | exact resolve eq19 eq107012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq107012
  have eq107479 : y = (M.op x y) := by grind
  clear eq107248
  have eq107733 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq107479 eq21
    | exact resolve eq21 eq107479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq107479
  have eq108146 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq107733
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq107733
    | exact resolve eq107733 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq107733
  have eq108147 : False := by grind
  exact eq108147
