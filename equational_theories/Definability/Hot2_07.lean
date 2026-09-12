import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation695`: `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pxy_pyx_Equation695 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law695 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law695.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X2) X1))) = X0 := by
    intro X0 X1 X2
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 X1) X2) X0
       have i₂ := eq14 (M.op X0 X0) X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq36
  have eq70 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq67
       have i₂ := eq70 y x
       grind)
    | exact superpose eq70 eq67
    | (have j1 := eq70 x x
       grind)
    | exact resolve eq67 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq101
  have eq347 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq51 (M.op X2 X2) X1 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq621 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq102 eq70
    | (have j0 := eq70 x (σ x)
       grind)
    | exact resolve eq70 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq622 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq621
    | exact resolve eq621 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq625 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq622
       have r₂ := eq27
       grind)
    | exact resolve eq622 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq628 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq625 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq625
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq625
       grind)
    | exact resolve eq13 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq628 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq642 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq635 eq49
    | exact resolve eq49 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq635
  have eq717 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq625 eq642
    | exact resolve eq642 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625 eq642
  have eq730 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by grind
  clear eq717
  have eq732 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq730
    | exact resolve eq730 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq730
  have eq735 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70 x x
       have i₂ := eq732
       grind)
    | exact superpose eq732 eq70
    | (have j0 := eq70 x x
       grind)
    | exact resolve eq70 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq736 : x = (M.op x x) := by grind
  clear eq735
  have eq740 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq736
       grind)
    | exact superpose eq736 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq736
       grind)
    | exact resolve eq13 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op x X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x
       have i₂ := eq736
       grind)
    | exact superpose eq736 eq14
    | exact resolve eq14 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq740 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq808 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq749 x
       grind)
    | exact superpose eq749 eq43
    | exact resolve eq43 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq810 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq749 sF0
       grind)
    | exact superpose eq749 eq45
    | exact resolve eq45 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq749
  have eq813 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq808
       have i₂ := eq736
       grind)
    | exact superpose eq736 eq808
    | exact resolve eq808 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq815 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq813
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq813
    | exact resolve eq813 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq813
  have eq820 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq815 eq70
    | (have j0 := eq70 x (σ x)
       grind)
    | exact resolve eq70 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq815
  have eq821 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq820
  have eq881 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq821 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq821
       grind)
    | exact resolve eq13 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq881 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq1033 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq894 eq810
    | exact resolve eq810 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq894
  have eq1178 : ∀ X0 : G, (M.op y (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq741 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq741
    | (have j0 := eq741 y X0
       grind)
    | exact resolve eq741 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1179 : ∀ X0 : G, (M.op x (M.op X0 x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq741 x X0
       have i₂ := eq736
       grind)
    | exact superpose eq736 eq741
    | exact resolve eq741 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1191 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op (M.op X0 X0) (M.op x X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq741 X1 (M.op X2 X2)
       have i₂ := eq347 (M.op x X1) X0 X2
       grind)
    | (have i₁ := eq741 X1 (M.op X2 X2)
       have i₂ := eq347 (M.op x X1) X2 X0
       grind)
    | exact superpose eq347 eq741
    | exact resolve eq741 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq1212 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq1191 X0 x X2
       have i₂ := eq741 x (M.op X0 X0)
       grind)
    | exact superpose eq741 eq1191
    | exact resolve eq1191 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1219 : y = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1178 eq741
    | exact resolve eq741 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq1178
  have eq1224 : (σ y) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1219 eq1033
    | exact resolve eq1033 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033 eq1219
  have eq1227 : (σ y) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1224
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1224
    | exact resolve eq1224 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1224
  have eq1271 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq1212 X0 x
       have i₂ := eq736
       grind)
    | exact superpose eq736 eq1212
    | exact resolve eq1212 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq1212
  have eq1391 : x = (σ x) := by
    first
    | exact superpose eq821 eq1271
    | exact resolve eq1271 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821 eq1271
  have eq1478 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq1391 eq26
    | exact resolve eq26 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1497 : (σ y) = (M.op (σ (M.op x y)) x) := by
    first
    | exact superpose eq1391 eq1227
    | exact resolve eq1227 eq1391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227 eq1391
  have eq1584 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq1497 eq1179
    | exact resolve eq1179 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179 eq1497
  have eq1589 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1478 eq1584
    | exact resolve eq1584 eq1478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478 eq1584
  have eq1592 : False := by grind
  exact eq1592

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_x_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37
  have eq59 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq63 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq59
    | (have j0 := eq59 X0 X1
       grind)
    | exact resolve eq59 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq89 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63
    | exact resolve eq63 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq144 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq125 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq125
    | (have j0 := eq125 X0 X1
       grind)
    | exact resolve eq125 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq125
  have eq149 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq144 X0 X1
       have j1 := eq89 X1 X0
       grind)
    | (have r₁ := eq144 X1 X0
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq144 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq144 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq144
  have eq165 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq149
    | exact resolve eq149 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq149 (σ X0) X1
       grind)
    | exact superpose eq149 eq15
    | (have j1 := eq149 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq193 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq165 (τ X1) X0
       grind)
    | exact superpose eq165 eq18
    | (have j1 := eq165 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq165
  have eq255 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq193 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq193
    | exact resolve eq193 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq277 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq255 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq255
    | (have j0 := eq255 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq255 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1046 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq170 x y
       grind)
    | exact superpose eq170 eq16
    | (have j1 := eq170 x y
       grind)
    | exact resolve eq16 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq1081 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1046
       have i₂ := eq277 y x
       grind)
    | exact superpose eq277 eq1046
    | (have j1 := eq277 (σ x) (σ y)
       grind)
    | (have r₁ := eq1046
       have r₂ := eq277 y x
       grind)
    | (have r₁ := eq1046
       have r₂ := eq277 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1046
       have r₂ := eq277 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1046 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq1046
  have eq1082 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1081
  have eq1086 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1082
       grind)
    | exact superpose eq1082 eq10
    | exact resolve eq10 eq1082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1131 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1086
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1086
    | exact resolve eq1086 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1132 : x = y := by grind
  clear eq1131
  have eq1196 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1132
       grind)
    | exact superpose eq1132 eq16
    | exact resolve eq16 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1197 : False := by grind
  exact eq1197

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) := by
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
  have eq71 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq36
  have eq84 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq77
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq701
    | exact resolve eq701 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq705 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq702
       have r₂ := eq27
       grind)
    | exact resolve eq702 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq707 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq705
    | exact resolve eq705 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq709 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq707
    | exact resolve eq707 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq715 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq709 eq71
    | (have r₁ := eq71
       have r₂ := eq709
       grind)
    | exact resolve eq71 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq709
  have eq719 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq715
  have eq758 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq719
       have r₂ := eq718
       grind)
    | exact resolve eq719 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq719
  have eq797 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq758 eq84
    | exact resolve eq84 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq805 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq797
    | exact resolve eq797 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq797
  have eq809 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq805
       have r₂ := eq70
       grind)
    | exact resolve eq805 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq812 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq809
       grind)
    | exact superpose eq809 eq77
    | exact resolve eq77 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq809
       grind)
    | exact superpose eq809 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq814 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq813
  have eq816 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq814
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq814
    | exact resolve eq814 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq817 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq816
  have eq818 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq812
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq812
    | exact resolve eq812 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq821 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq817
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq817
    | exact resolve eq817 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq825 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq821 eq51
    | (have r₁ := eq51
       have r₂ := eq821
       grind)
    | exact resolve eq51 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq830 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq825
  have eq841 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq818 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq842 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq841
  have eq846 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq842
    | exact resolve eq842 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq847 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq846
  have eq852 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq847
    | exact resolve eq847 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq861 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq852 eq27
    | exact resolve eq27 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq886 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq830 eq84
    | exact resolve eq84 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq897 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq886
    | exact resolve eq886 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq900 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq897
       have r₂ := eq50
       grind)
    | exact resolve eq897 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq906 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq900
       grind)
    | exact superpose eq900 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq907 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq906
  have eq909 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq907
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq907
    | exact resolve eq907 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq910 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq909
  have eq914 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq910
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq910
    | exact resolve eq910 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq910
  have eq924 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq914 eq20
    | exact resolve eq20 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq929 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq914 eq70
    | (have r₁ := eq70
       have r₂ := eq914
       grind)
    | exact resolve eq70 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq941 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq914
  have eq942 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq929
  have eq952 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq924
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq924
    | exact resolve eq924 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq976 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq952 eq861
    | (have r₁ := eq861
       have r₂ := eq952
       grind)
    | exact resolve eq861 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq952
  have eq979 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq976
  have eq980 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq979
  have eq1001 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq980 eq51
    | (have r₁ := eq51
       have r₂ := eq980
       grind)
    | exact resolve eq51 eq980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq980
  have eq1008 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1001
  have eq1048 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1008 eq84
    | exact resolve eq84 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq1008
  have eq1063 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1048
    | exact resolve eq1048 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1048
  have eq1066 : y = (k y x) := by
    first
    | (have r₁ := eq1063
       have r₂ := eq50
       grind)
    | exact resolve eq1063 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1063
  have eq1071 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq1066
       grind)
    | exact superpose eq1066 eq77
    | exact resolve eq77 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1076 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1071
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1071
    | exact resolve eq1071 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1071
  have eq1089 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1076 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1089
  have eq1092 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1090
    | exact resolve eq1090 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1095 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1092
    | exact resolve eq1092 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1092
  have eq1101 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1095 eq71
    | (have r₁ := eq71
       have r₂ := eq1095
       grind)
    | exact resolve eq71 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1108 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1095
  have eq1109 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1101
  have eq1110 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1076 eq1109
    | exact resolve eq1109 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076 eq1109
  have eq1111 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1110
  have eq1160 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1111
       have r₂ := eq1108
       grind)
    | exact resolve eq1111 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108 eq1111
  have eq1164 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1160 eq27
    | exact resolve eq27 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1160
  have eq2576 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq942
       have r₂ := eq941
       grind)
    | exact resolve eq942 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq2577 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2576
       have i₂ := eq1066
       grind)
    | exact superpose eq1066 eq2576
    | exact resolve eq2576 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066 eq2576
  have eq2578 : x = (M.op x y) := by
    first
    | (have r₁ := eq2577
       have r₂ := eq941
       grind)
    | exact resolve eq2577 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq2577
  have eq2580 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2578 eq20
    | exact resolve eq20 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2578
  have eq2615 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2580
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2580
    | exact resolve eq2580 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2580
  have eq2617 : False := by grind
  exact eq2617

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
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
  have eq30 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
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
  have eq34 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
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
  have eq39 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq25
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86 x y
       grind)
    | exact superpose eq86 eq16
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (M.op (σ X0) X1) (σ X2)) ∨ (M.op (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 X1 X2
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq430 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 x
       have i₂ := eq86 x x
       grind)
    | exact superpose eq86 eq39
    | (have j1 := eq86 X0 X0
       grind)
    | exact resolve eq39 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq441 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq430 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq446 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (k X0 X0) X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq441 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq441
    | (have j0 := eq441 X0
       grind)
    | exact resolve eq441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq470 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq89 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq509 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq470 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq470
    | (have j0 := eq470 X0 X1
       grind)
    | exact resolve eq470 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq513 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X1) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq509 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq509
    | (have j0 := eq509 (τ X0) (τ X1)
       grind)
    | exact resolve eq509 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq513 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq513
    | (have j0 := eq513 X0 X1
       grind)
    | exact resolve eq513 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq5505 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (k (k X0 X0) X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    grind
  clear eq446
  have eq5531 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k (k X0 X0) X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq5505 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq5505
    | (have j0 := eq5505 X0
       grind)
    | exact resolve eq5505 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5505
  have eq14405 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq161
  have eq14429 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k (k X0 (τ (σ X0))) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq14405 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14405
  have eq14438 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14429 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14429
    | (have j0 := eq14429 X0
       grind)
    | exact resolve eq14429 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14429
  have eq15735 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (σ (k (k X0 X0) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq14438 X0
       grind)
    | exact superpose eq14438 eq39
    | (have j1 := eq14438 X0
       grind)
    | exact resolve eq39 eq14438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14438
  have eq15806 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (τ (M.op (σ X0) (σ X0))) X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq15735 X0
       have i₂ := eq10 (k (k X0 X0) X0)
       grind)
    | exact superpose eq10 eq15735
    | (have j0 := eq15735 X0
       grind)
    | exact resolve eq15735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15735
  have eq16327 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (k (τ (M.op (σ X0) (σ X0))) X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq15806 X0
       grind)
    | exact superpose eq15806 eq39
    | (have j1 := eq15806 X0
       grind)
    | exact resolve eq39 eq15806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15806
  have eq16406 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (k (k X0 X0) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq16327 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16327
    | (have j0 := eq16327 X0
       grind)
    | exact resolve eq16327 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16327
  have eq28301 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) ∨ (k (k X0 X0) X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq5531 X0
       grind)
    | exact superpose eq5531 eq39
    | (have j1 := eq5531 X0
       grind)
    | exact resolve eq39 eq5531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq5531
  have eq28429 : ∀ X0 : G, (k (k X0 X0) X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) ∨ (k (k X0 X0) X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28301 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq28301
    | (have j0 := eq28301 X0
       grind)
    | exact resolve eq28301 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28301
  have eq28430 : ∀ X0 : G, (k (k X0 X0) X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq28429 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28429
  have eq28706 : ∀ X0 : G, (k (k (τ X0) (τ X0)) (τ X0)) = (τ (M.op (k X0 (σ (τ X0))) (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq28430 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq28430
    | exact resolve eq28430 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28772 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ (k X0 X0)) (σ X0))
       have i₂ := eq28430 X0
       grind)
    | exact superpose eq28430 eq11
    | exact resolve eq11 eq28430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28430
  have eq28882 : ∀ X0 : G, (k (k (τ X0) (τ X0)) (τ X0)) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq28706 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28706
    | exact resolve eq28706 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28706
  have eq28917 : ∀ X0 : G, (k (τ (k X0 X0)) (τ X0)) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq28882 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq28882
    | exact resolve eq28882 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28882
  have eq28946 : ∀ X0 : G, (τ (k (k X0 X0) X0)) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq28917 X0
       have i₂ := eq35 X0 (k X0 X0)
       grind)
    | exact superpose eq35 eq28917
    | exact resolve eq28917 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28917
  have eq29048 : ∀ X0 : G, (k (k X0 X0) X0) = (σ (τ (M.op (k X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k (k X0 X0) X0)
       have i₂ := eq28946 X0
       grind)
    | exact superpose eq28946 eq11
    | exact resolve eq11 eq28946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29215 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq29048 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq29048
    | exact resolve eq29048 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29048
  have eq29396 : ∀ X0 : G, (k (τ (k X0 X0)) (τ X0)) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq29215 (τ X0)
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq29215
    | exact resolve eq29215 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29604 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq29396 X0
       have i₂ := eq35 X0 (k X0 X0)
       grind)
    | exact superpose eq35 eq29396
    | exact resolve eq29396 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29396
  have eq29686 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq29604 X0
       have i₂ := eq28946 X0
       grind)
    | exact superpose eq28946 eq29604
    | exact resolve eq29604 eq28946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28946 eq29604
  have eq29814 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (k (σ (k X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28772 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq28772
    | exact resolve eq28772 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30135 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (k (k X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq29814 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq29814
    | exact resolve eq29814 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29814
  have eq30203 : ∀ X0 : G, (M.op (σ (σ (k X0 X0))) (σ (σ X0))) = (σ (σ (M.op (k X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq30135 X0
       have i₂ := eq29215 X0
       grind)
    | exact superpose eq29215 eq30135
    | exact resolve eq30135 eq29215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30135
  have eq35043 : ∀ X0 : G, (M.op (σ (σ (k (τ X0) (τ X0)))) (σ X0)) = (σ (σ (M.op (k (τ X0) (τ X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq30203 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30203
    | exact resolve eq30203 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30203
  have eq35226 : ∀ X0 : G, (M.op (σ (σ (τ (k X0 X0)))) (σ X0)) = (σ (σ (M.op (τ (k X0 X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq35043 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq35043
    | exact resolve eq35043 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35043
  have eq35292 : ∀ X0 : G, (σ (σ (τ (M.op (k X0 X0) X0)))) = (M.op (σ (σ (τ (k X0 X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq35226 X0
       have i₂ := eq29686 X0
       grind)
    | exact superpose eq29686 eq35226
    | exact resolve eq35226 eq29686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35226
  have eq35333 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (σ (τ (M.op (k X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq35292 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq35292
    | exact resolve eq35292 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35292
  have eq35361 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq35333 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq35333
    | exact resolve eq35333 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35333
  have eq72384 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (k (σ (τ (M.op (σ (τ X0)) (σ (τ X0))))) X0) ∨ (k (τ X0) (τ X0)) = (τ (M.op (σ (τ X0)) (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ (M.op (σ (τ X0)) (σ (τ X0))))
       have i₂ := eq16406 (τ X0)
       grind)
    | exact superpose eq16406 eq19
    | (have j1 := eq16406 (τ X0)
       grind)
    | exact resolve eq19 eq16406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16406
  have eq72465 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (k (M.op (σ (τ X0)) (σ (τ X0))) X0) ∨ (k (τ X0) (τ X0)) = (τ (M.op (σ (τ X0)) (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq72384 X0
       have i₂ := eq11 (M.op (σ (τ X0)) (σ (τ X0)))
       grind)
    | exact superpose eq11 eq72384
    | (have j0 := eq72384 X0
       grind)
    | exact resolve eq72384 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72384
  have eq72665 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (k (k (τ X0) (τ X0)) (τ X0))) ∨ (k (τ X0) (τ X0)) = (τ (M.op (σ (τ X0)) (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq72465 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq72465
    | (have j0 := eq72465 X0
       grind)
    | exact resolve eq72465 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72465
  have eq72792 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (k (τ X0) (τ X0)) = (τ (M.op (σ (τ X0)) (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq72665 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq72665
    | (have j0 := eq72665 X0
       grind)
    | exact resolve eq72665 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72665
  have eq72897 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (k (τ X0) (τ X0)) = (τ (M.op (σ (τ X0)) (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq72792 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq72792
    | (have j0 := eq72792 X0
       grind)
    | exact resolve eq72792 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq72792
  have eq72978 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (k X0 X0) X0) ∨ (k (τ X0) (τ X0)) = (τ (M.op (σ (τ X0)) (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq72897 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq72897
    | (have j0 := eq72897 X0
       grind)
    | exact resolve eq72897 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72897
  have eq73034 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k (τ X0) (τ X0)) = (τ (M.op (σ (τ X0)) (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq72978 X0
       have i₂ := eq29215 X0
       grind)
    | exact superpose eq29215 eq72978
    | (have j0 := eq72978 X0
       grind)
    | exact resolve eq72978 eq29215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72978
  have eq73085 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k (τ X0) (τ X0)) = (τ (M.op (σ (τ X0)) (σ (τ X0)))) := by
    intro X0
    grind
  clear eq73034
  have eq73129 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq73085 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq73085
    | (have j0 := eq73085 X0
       grind)
    | exact resolve eq73085 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73085
  have eq73167 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq73129 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq73129
    | (have j0 := eq73129 X0
       grind)
    | exact resolve eq73129 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73129
  have eq73277 : ∀ X0 X1 : G, (k (k X0 X0) (σ X1)) = (σ (k (τ (M.op X0 X0)) X1)) ∨ (M.op (M.op X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (k X0 X0) X1
       have i₂ := eq73167 X0
       grind)
    | exact superpose eq73167 eq18
    | (have j1 := eq73167 X0
       grind)
    | exact resolve eq18 eq73167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73167
  have eq73494 : ∀ X0 X1 : G, (k (k X0 X0) (σ X1)) = (k (M.op X0 X0) (σ X1)) ∨ (M.op (M.op X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq73277 X0 X1
       have i₂ := eq18 (M.op X0 X0) X1
       grind)
    | exact superpose eq18 eq73277
    | (have j0 := eq73277 X0 X1
       grind)
    | exact resolve eq73277 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq73277
  have eq99837 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq29215 (σ X0)
       have i₂ := eq73494 (σ X0) X0
       grind)
    | exact superpose eq73494 eq29215
    | (have j1 := eq73494 (σ X0) x
       grind)
    | exact resolve eq29215 eq73494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73494
  have eq99904 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq99837 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq99837
    | (have j0 := eq99837 X0
       grind)
    | exact resolve eq99837 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99837
  have eq99939 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq99904 X0
       have i₂ := eq28772 X0
       grind)
    | exact superpose eq28772 eq99904
    | (have j0 := eq99904 X0
       grind)
    | exact resolve eq99904 eq28772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99904
  have eq99972 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) ∨ (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq99939 X0
       have i₂ := eq29215 X0
       grind)
    | exact superpose eq29215 eq99939
    | (have j0 := eq99939 X0
       grind)
    | exact resolve eq99939 eq29215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99939
  have eq99998 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) ∨ (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    grind
  clear eq99972
  have eq100017 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq99998 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq99998
    | (have j0 := eq99998 X0
       grind)
    | exact resolve eq99998 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99998
  have eq100031 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq100017 X0
       have i₂ := eq28772 X0
       grind)
    | exact superpose eq28772 eq100017
    | (have j0 := eq100017 X0
       grind)
    | exact resolve eq100017 eq28772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28772 eq100017
  have eq100042 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) ∨ (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq100031 X0
       have i₂ := eq29215 X0
       grind)
    | exact superpose eq29215 eq100031
    | (have j0 := eq100031 X0
       grind)
    | exact resolve eq100031 eq29215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29215 eq100031
  have eq100043 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq100042 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100042
  have eq100096 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (k (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq100043 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq100043
    | exact resolve eq100043 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100043
  have eq100283 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (k X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq100096 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq100096
    | exact resolve eq100096 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100096
  have eq100321 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (τ (M.op (k X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq100283 X0
       have i₂ := eq29686 X0
       grind)
    | exact superpose eq29686 eq100283
    | exact resolve eq100283 eq29686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29686 eq100283
  have eq100340 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq100321 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq100321
    | exact resolve eq100321 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100321
  have eq413121 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq560 X1 X0
       grind)
    | exact superpose eq560 eq13
    | (have j0 := eq13 (τ X1) (τ X0)
       have j1 := eq560 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq560 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X0)
       have r₂ := eq560 X0 X0
       grind)
    | exact resolve eq13 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413221 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq560 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq413222 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq413221 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413221
  have eq413223 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq413121 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413121
  have eq413224 : ∀ X0 X1 : G, (τ X0) = (k (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq413223 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413223
  have eq413245 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X0)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq413224 X0 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq413224
    | (have j0 := eq413224 X0 X1
       grind)
    | exact resolve eq413224 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq413224
  have eq415283 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq413222 X0
       grind)
    | exact superpose eq413222 eq34
    | (have j1 := eq413222 X0
       grind)
    | exact resolve eq34 eq413222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq413222
  have eq415573 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq415283 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq415283
    | (have j0 := eq415283 X0
       grind)
    | exact resolve eq415283 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415283
  have eq415574 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq415573 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415573
  have eq415793 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq415574 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq415574
    | exact resolve eq415574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415945 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq415574 X0
       grind)
    | exact superpose eq415574 eq10
    | exact resolve eq10 eq415574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415574
  have eq416617 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq415793 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq415793
    | exact resolve eq415793 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415793
  have eq419036 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq35361 X0
       have i₂ := eq416617 X0
       grind)
    | exact superpose eq416617 eq35361
    | exact resolve eq35361 eq416617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35361
  have eq419118 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq416617 X0
       grind)
    | exact superpose eq416617 eq10
    | exact resolve eq10 eq416617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419751 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq419118 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq419118
    | exact resolve eq419118 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419118
  have eq419800 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq419036 X0
       have i₂ := eq100340 X0
       grind)
    | exact superpose eq100340 eq419036
    | exact resolve eq419036 eq100340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100340 eq419036
  have eq420924 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq419751 (σ X0)
       grind)
    | exact superpose eq419751 eq15
    | exact resolve eq15 eq419751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421262 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq420924 X0
       have i₂ := eq416617 X0
       grind)
    | exact superpose eq416617 eq420924
    | exact resolve eq420924 eq416617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416617 eq420924
  have eq706568 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq413245 X0 X1
       grind)
    | exact superpose eq413245 eq11
    | (have j1 := eq413245 X0 X1
       grind)
    | exact resolve eq11 eq413245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413245
  have eq707150 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ X1) = (M.op (τ X0) (τ X0)) ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq706568 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq706568
    | (have j0 := eq706568 X0 X1
       grind)
    | exact resolve eq706568 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706568
  have eq707658 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq707150 X0 X1
       have i₂ := eq415945 X0
       grind)
    | exact superpose eq415945 eq707150
    | (have j0 := eq707150 X0 X1
       grind)
    | exact resolve eq707150 eq415945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415945 eq707150
  have eq708111 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq707658 X0 X1
       have i₂ := eq419751 X0
       grind)
    | exact superpose eq419751 eq707658
    | (have j0 := eq707658 X0 X1
       grind)
    | exact resolve eq707658 eq419751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419751 eq707658
  have eq718597 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq708111 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq708111
    | (have j0 := eq708111 X1 (σ X0)
       grind)
    | exact resolve eq708111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708111
  have eq726981 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 (τ (σ X1)))) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq718597 X0 (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq718597
    | (have j0 := eq718597 X0 (σ X1)
       grind)
    | exact resolve eq718597 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718597
  have eq728010 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq726981 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq726981
    | (have j0 := eq726981 X0 X1
       grind)
    | exact resolve eq726981 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726981
  have eq728429 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq728010 X0 X1
       have i₂ := eq421262 X1
       grind)
    | exact superpose eq421262 eq728010
    | (have j0 := eq728010 X0 X1
       grind)
    | exact resolve eq728010 eq421262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728010
  have eq728800 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq728429 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq728429
    | (have j0 := eq728429 X0 X1
       grind)
    | exact resolve eq728429 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728429
  have eq733059 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq140
       have i₂ := eq728800 x y
       grind)
    | exact superpose eq728800 eq140
    | (have j1 := eq728800 x y
       grind)
    | (have r₁ := eq140
       have r₂ := eq728800 x y
       grind)
    | exact resolve eq140 eq728800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq728800
  have eq733560 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq733059
  have eq733931 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq145 x y
       grind)
    | (have r₁ := eq733560
       have r₂ := eq145 x y
       grind)
    | exact resolve eq733560 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq733560
  have eq734367 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq733931
       have i₂ := eq421262 y
       grind)
    | exact superpose eq421262 eq733931
    | exact resolve eq733931 eq421262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733931
  have eq742667 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq734367
       grind)
    | exact superpose eq734367 eq16
    | exact resolve eq16 eq734367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742754 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq734367
       grind)
    | exact superpose eq734367 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq734367
       grind)
    | exact resolve eq13 eq734367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734367
  have eq742876 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq742754
  have eq742944 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq742876
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq742876
    | exact resolve eq742876 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742876
  have eq743044 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq742944
       have i₂ := eq421262 y
       grind)
    | exact superpose eq421262 eq742944
    | exact resolve eq742944 eq421262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421262 eq742944
  have eq743045 : x = (M.op y y) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq743044
  have eq744428 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq419800 y
       have i₂ := eq743045
       grind)
    | exact superpose eq743045 eq419800
    | exact resolve eq419800 eq743045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743045
  have eq744607 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq744428
       have r₂ := eq16
       grind)
    | exact resolve eq744428 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744428
  have eq745791 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq509 x y
       have i₂ := eq744607
       grind)
    | exact superpose eq744607 eq509
    | (have j0 := eq509 x y
       grind)
    | exact resolve eq509 eq744607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq744607
  have eq746738 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq745791
       have r₂ := eq742667
       grind)
    | exact resolve eq745791 eq742667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745791
  have eq754900 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq742667
       have i₂ := eq746738
       grind)
    | exact superpose eq746738 eq742667
    | exact resolve eq742667 eq746738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742667 eq746738
  have eq755034 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq754900
  have eq755035 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq755034
  have eq756808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq419800 y
       have i₂ := eq755035
       grind)
    | exact superpose eq755035 eq419800
    | exact resolve eq419800 eq755035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755035
  have eq756987 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq756808
       have r₂ := eq16
       grind)
    | exact resolve eq756808 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756808
  have eq757154 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq756987
       grind)
    | exact superpose eq756987 eq10
    | exact resolve eq10 eq756987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756987
  have eq758071 : x = (M.op y y) := by
    first
    | (have i₁ := eq757154
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq757154
    | exact resolve eq757154 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757154
  have eq760739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq419800 y
       have i₂ := eq758071
       grind)
    | exact superpose eq758071 eq419800
    | exact resolve eq419800 eq758071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419800 eq758071
  have eq760918 : False := by grind
  exact eq760918

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxx_pxy_pyx_Equation840 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law840 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
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
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
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
  have eq175 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq179 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq181 eq177
    | exact resolve eq177 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq182 eq177
    | exact resolve eq177 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq622 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq627 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq635 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq635 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq635 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq635 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq681 : y ≠ y ∨ y = (M.op (M.op x y) y) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq181 eq12
    | (have j0 := eq12 y (M.op x y)
       grind)
    | (have r₁ := eq12 y (M.op x y)
       have r₂ := eq181
       grind)
    | exact resolve eq12 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq188 eq12
    | (have j0 := eq12 (M.op x y) y
       grind)
    | (have r₁ := eq12 (M.op x y) y
       have r₂ := eq188
       grind)
    | exact resolve eq12 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq182 eq12
    | (have j0 := eq12 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq182
       grind)
    | exact resolve eq12 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq191 eq12
    | (have j0 := eq12 (M.op (σ x) (σ y)) (σ y)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq191
       grind)
    | exact resolve eq12 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq688
  have eq693 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq686
  have eq695 : (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by grind
  clear eq683
  have eq697 : y = (M.op (M.op x y) y) ∨ y = (k y (M.op x y)) := by grind
  clear eq681
  have eq703 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq182 eq691
    | exact resolve eq691 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq705 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq191 eq693
    | exact resolve eq693 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq707 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq181 eq695
    | exact resolve eq695 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq695
  have eq709 : y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq188 eq697
    | exact resolve eq697 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq714 : (τ (σ y)) = (k y (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq705 eq107
    | exact resolve eq107 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq705
  have eq715 : y = (k y (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq714
    | exact resolve eq714 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq717 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq709 eq41
    | exact resolve eq41 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq709
  have eq718 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq717
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq717
    | exact resolve eq717 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq721 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq703 eq152
    | exact resolve eq152 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq703
  have eq723 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq707 eq40
    | exact resolve eq40 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq707
  have eq724 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq723
    | exact resolve eq723 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq786 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq622
       grind)
    | exact superpose eq622 eq39
    | exact resolve eq39 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq786
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq786
    | exact resolve eq786 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq789 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq787
    | exact resolve eq787 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq789 eq627
    | exact resolve eq627 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq838 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq831
       have r₂ := eq27
       grind)
    | exact resolve eq831 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq847 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq838 eq177
    | exact resolve eq177 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq852 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq847
    | exact resolve eq847 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq862 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq177
    | exact resolve eq177 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq867 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq862
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq862
    | exact resolve eq862 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq873 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq867 eq27
    | exact resolve eq27 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq875 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq867 eq179
    | (have r₁ := eq179
       have r₂ := eq867
       grind)
    | exact resolve eq179 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq877 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq867 eq191
    | exact resolve eq191 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq867
  have eq886 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq875
  have eq888 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq877 eq886
    | exact resolve eq886 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq886
  have eq909 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq888 eq789
    | exact resolve eq789 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq888
  have eq915 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq909
  have eq921 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq915
       have r₂ := eq873
       grind)
    | exact resolve eq915 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq915
  have eq946 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq921
       grind)
    | exact superpose eq921 eq177
    | exact resolve eq177 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq951 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq946
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq946
    | exact resolve eq946 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq952 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq951
  have eq961 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq952 eq182
    | exact resolve eq182 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq969 : y = (k y (τ (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq952 eq715
    | exact resolve eq715 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq970 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq952 eq721
    | exact resolve eq721 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq973 : x = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq970
    | exact resolve eq970 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq974 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq969
    | exact resolve eq969 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq1101 : x ≠ x ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq664 y x
       have i₂ := eq973
       grind)
    | exact superpose eq973 eq664
    | (have j0 := eq664 y x
       grind)
    | (have r₁ := eq664 y x
       have r₂ := eq973
       grind)
    | exact resolve eq664 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq1102 : x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1101
  have eq1103 : x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1102
    | exact resolve eq1102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1104 : x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1103
  have eq1109 : y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq622
       have i₂ := eq974
       grind)
    | exact superpose eq974 eq622
    | exact resolve eq622 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq974
  have eq1114 : y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1109
  have eq1120 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1104 eq1114
    | exact resolve eq1114 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq1114
  have eq1125 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1120 eq31
    | exact resolve eq31 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1120
  have eq1176 : x = y ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1125
    | exact resolve eq1125 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1177 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1176
  have eq1182 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1177
       grind)
    | exact superpose eq1177 eq24
    | exact resolve eq24 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1186 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq178
       have i₂ := eq1177
       grind)
    | exact superpose eq1177 eq178
    | (have r₁ := eq178
       have r₂ := eq1177
       grind)
    | exact resolve eq178 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1188 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq188
       have i₂ := eq1177
       grind)
    | exact superpose eq1177 eq188
    | exact resolve eq188 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq1198 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1186
  have eq1199 : (M.op x y) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1188 eq1198
    | exact resolve eq1198 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188 eq1198
  have eq1202 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1182
    | exact resolve eq1182 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1260 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1199 eq39
    | exact resolve eq39 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1263 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1260
    | exact resolve eq1260 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq1265 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1202 eq1263
    | exact resolve eq1263 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq1284 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1265 eq627
    | exact resolve eq627 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq1290 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1284
  have eq1297 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq961 eq1290
    | exact resolve eq1290 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq1290
  have eq1298 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1297
  have eq1330 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1298 eq177
    | exact resolve eq177 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1337 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1330
    | exact resolve eq1330 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330
  have eq1342 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1337 eq27
    | exact resolve eq27 eq1337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq1361 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1202 eq1342
    | (have r₁ := eq1342
       have r₂ := eq1202
       grind)
    | exact resolve eq1342 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq1362 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1361
  have eq1363 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1362
  have eq1364 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq952 eq1363
    | exact resolve eq1363 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq1365 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1364
  have eq1368 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1365 eq27
    | exact resolve eq27 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1371 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1365 eq182
    | exact resolve eq182 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1380 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1365 eq721
    | exact resolve eq721 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721 eq1365
  have eq1384 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1380
    | exact resolve eq1380 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1380
  have eq1388 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1202 eq1368
    | exact resolve eq1368 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202 eq1368
  have eq1389 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1388
  have eq1655 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq674 x y
       have i₂ := eq1384
       grind)
    | exact superpose eq1384 eq674
    | (have j0 := eq674 x x
       grind)
    | (have r₁ := eq674 x y
       have r₂ := eq1384
       grind)
    | exact resolve eq674 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1656 : x ≠ x ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq664 y x
       have i₂ := eq1384
       grind)
    | exact superpose eq1384 eq664
    | (have j0 := eq664 y x
       grind)
    | (have r₁ := eq664 y x
       have r₂ := eq1384
       grind)
    | exact resolve eq664 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq1657 : x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1656
  have eq1658 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1655
  have eq1660 : x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1657
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1657
    | exact resolve eq1657 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1657
  have eq1661 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1660
  have eq1662 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1658
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1658
    | exact resolve eq1658 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1658
  have eq1663 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1662
  have eq1690 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1661
       have i₂ := eq1177
       grind)
    | exact superpose eq1177 eq1661
    | exact resolve eq1661 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq1707 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1690
  have eq1712 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1707
       have r₂ := eq1389
       grind)
    | exact resolve eq1707 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707
  have eq1805 : (M.op x y) = (M.op (M.op x y) (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq190 x
       have i₂ := eq1663
       grind)
    | exact superpose eq1663 eq190
    | exact resolve eq190 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq1663
  have eq1814 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1661 eq1805
    | exact resolve eq1805 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661 eq1805
  have eq1856 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1814 eq1712
    | exact resolve eq1712 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712 eq1814
  have eq1871 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1856
  have eq1873 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1871
       have r₂ := eq1389
       grind)
    | exact resolve eq1871 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389 eq1871
  have eq1876 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq1873
       grind)
    | exact superpose eq1873 eq22
    | exact resolve eq22 eq1873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1886 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq1876
    | exact resolve eq1876 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq1898 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1886 eq718
    | exact resolve eq718 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq1899 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1886 eq724
    | exact resolve eq724 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq2051 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1898 eq627
    | exact resolve eq627 eq1898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627 eq1898
  have eq2060 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq2051
  have eq2070 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1371 eq2060
    | exact resolve eq2060 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371 eq2060
  have eq2071 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2070
  have eq2086 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1899 eq674
    | (have j0 := eq674 (σ x) (σ x)
       grind)
    | (have r₁ := eq674 (σ x) (σ y)
       have r₂ := eq1899
       grind)
    | exact resolve eq674 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq2087 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1899 eq664
    | (have j0 := eq664 (σ y) (σ x)
       grind)
    | (have r₁ := eq664 (σ y) (σ x)
       have r₂ := eq1899
       grind)
    | exact resolve eq664 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq1899
  have eq2088 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq2087
  have eq2089 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq2086
  have eq2091 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq2088
    | exact resolve eq2088 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088
  have eq2092 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq2089
    | exact resolve eq2089 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089
  have eq2096 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq952 eq2091
    | exact resolve eq2091 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq2097 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2096
  have eq2098 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq952 eq2092
    | exact resolve eq2092 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952 eq2092
  have eq2099 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2098
  have eq2125 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2071 eq177
    | exact resolve eq177 eq2071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2071
  have eq2133 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2125
    | exact resolve eq2125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq2214 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2099 eq208
    | exact resolve eq208 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq2099
  have eq2218 : (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2133 eq2214
    | exact resolve eq2214 eq2133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133 eq2214
  have eq2221 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2097 eq2218
    | exact resolve eq2218 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097 eq2218
  have eq2224 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2221
    | exact resolve eq2221 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221
  have eq2225 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2224
  have eq2363 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2225 eq27
    | exact resolve eq27 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225
  have eq2383 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1886 eq2363
    | (have r₁ := eq2363
       have r₂ := eq1886
       grind)
    | exact resolve eq2363 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886 eq2363
  have eq2385 : y = (M.op x y) ∨ x = y := by grind
  clear eq2383
  have eq2403 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq2385
  have eq2407 : x = y := by
    first
    | (have r₁ := eq2403
       have r₂ := eq1873
       grind)
    | exact resolve eq2403 eq1873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873 eq2403
  have eq2415 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2407
       grind)
    | exact superpose eq2407 eq18
    | exact resolve eq18 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2416 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2407
       grind)
    | exact superpose eq2407 eq24
    | exact resolve eq24 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2407
  have eq2450 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2416
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2416
    | exact resolve eq2416 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416
  have eq2451 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2450 eq26
    | exact resolve eq26 eq2450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2450
  have eq2521 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq2415
       grind)
    | exact superpose eq2415 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq2415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2523 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq2415
       grind)
    | exact superpose eq2415 eq13
    | exact resolve eq13 eq2415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415
  have eq2544 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq2521
  have eq2555 : (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq2544
       have r₂ := eq2523
       grind)
    | exact resolve eq2544 eq2523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523 eq2544
  have eq2600 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2451 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq2451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2602 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2451 eq13
    | exact resolve eq13 eq2451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2451
  have eq2623 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2600
  have eq2632 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq2623
       have r₂ := eq2602
       grind)
    | exact resolve eq2623 eq2602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2602 eq2623
  have eq2681 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq2555
       grind)
    | exact superpose eq2555 eq39
    | exact resolve eq39 eq2555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq2555
  have eq2693 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2681
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2681
    | exact resolve eq2681 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2681
  have eq2695 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2632 eq2693
    | exact resolve eq2693 eq2632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2632 eq2693
  have eq2697 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2695
    | exact resolve eq2695 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2695
  have eq2699 : False := by grind
  exact eq2699

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_pxx_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X0 X0) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq63 (τ X0)
       grind)
    | exact superpose eq63 eq32
    | exact resolve eq32 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq75 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq68
    | exact resolve eq68 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq66
  have eq91 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq688 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) := by
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
  have eq697 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq688 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq688
    | (have j0 := eq688 X0 X1
       grind)
    | exact resolve eq688 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq688
  have eq705 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq680 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq680
    | (have j0 := eq680 X0 X1
       grind)
    | exact resolve eq680 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq719 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq705 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq705
    | (have j0 := eq705 X0 X1
       grind)
    | exact resolve eq705 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq722 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X1 (σ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq91
    | (have j0 := eq91 X1 (σ X0)
       grind)
    | (have r₁ := eq91 X0 (σ X0)
       have r₂ := eq77 X0
       grind)
    | exact resolve eq91 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq727 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq722 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq722
    | (have j0 := eq722 X0 X1
       grind)
    | exact resolve eq722 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq5105 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq719 x y
       grind)
    | exact superpose eq719 eq16
    | (have j1 := eq719 x y
       grind)
    | exact resolve eq16 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq5812 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq697 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq697
    | (have j0 := eq697 X1 (σ X0)
       grind)
    | exact resolve eq697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq5890 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5812 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5812
    | (have j0 := eq5812 X0 X1
       grind)
    | exact resolve eq5812 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5812
  have eq5898 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5890 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq5890
    | (have j0 := eq5890 X0 X1
       grind)
    | exact resolve eq5890 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5890
  have eq5901 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5898 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5898
    | (have j0 := eq5898 X0 X1
       grind)
    | exact resolve eq5898 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5898
  have eq8085 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq5105
       have i₂ := eq5901 y x
       grind)
    | exact superpose eq5901 eq5105
    | (have j1 := eq5901 y x
       grind)
    | (have r₁ := eq5105
       have r₂ := eq5901 y x
       grind)
    | (have r₁ := eq5105
       have r₂ := eq5901 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5105
       have r₂ := eq5901 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5105 eq5901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5105 eq5901
  have eq8086 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by grind
  clear eq8085
  have eq12778 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq8086
       grind)
    | exact superpose eq8086 eq10
    | exact resolve eq10 eq8086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8086
  have eq12871 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq12778
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq12778
    | exact resolve eq12778 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12778
  have eq12872 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12871
  have eq12875 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq12872
       grind)
    | exact superpose eq12872 eq12
    | (have j0 := eq12 x X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12872
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12872
       grind)
    | exact resolve eq12 eq12872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12979 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq727 y X0
       have i₂ := eq12872
       grind)
    | exact superpose eq12872 eq727
    | (have j0 := eq727 X0 x
       grind)
    | exact resolve eq727 eq12872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq12872
  have eq13162 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq12875 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12875
  have eq125042 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq12979 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12979
  have eq125062 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq125042
       grind)
    | exact superpose eq125042 eq16
    | exact resolve eq16 eq125042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125042
  have eq125192 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq125062
       have i₂ := eq13162
       grind)
    | exact superpose eq13162 eq125062
    | exact resolve eq125062 eq13162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13162 eq125062
  have eq125199 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq125192
  have eq125200 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq125199
  have eq125202 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq125200
       grind)
    | exact superpose eq125200 eq10
    | exact resolve eq10 eq125200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125200
  have eq125470 : x = y ∨ x = y := by
    first
    | (have i₁ := eq125202
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq125202
    | exact resolve eq125202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125202
  have eq125471 : x = y := by grind
  clear eq125470
  have eq125473 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq125471
       grind)
    | exact superpose eq125471 eq16
    | exact resolve eq16 eq125471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125471
  have eq125474 : False := by grind
  exact eq125474

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_y_pxy_x_pxy_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq14 X0 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ X0) (σ X1)
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq19
    | exact resolve eq19 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq86 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq86
    | exact resolve eq86 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq86
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq110 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 X0 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq143 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq16
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq183 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq110 (σ X0)
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq110
    | exact resolve eq110 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq143
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq143
    | exact resolve eq143 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq143
  have eq601 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq562
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq562
    | (have j1 := eq59 x y
       grind)
    | exact resolve eq562 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq562
  have eq602 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq601
  have eq606 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq110 x
       have i₂ := eq602
       grind)
    | exact superpose eq602 eq110
    | exact resolve eq110 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq183 x
       have i₂ := eq602
       grind)
    | exact superpose eq602 eq183
    | exact resolve eq183 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq6072 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq608
       grind)
    | exact superpose eq608 eq16
    | exact resolve eq16 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq6154 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6072
       have i₂ := eq606
       grind)
    | exact superpose eq606 eq6072
    | exact resolve eq6072 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq6072
  have eq6155 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq6154
  have eq6156 : (σ y) = (σ (M.op x x)) := by grind
  clear eq6155
  have eq6159 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq183 x
       have i₂ := eq6156
       grind)
    | exact superpose eq6156 eq183
    | exact resolve eq183 eq6156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq6167 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq6156
       grind)
    | exact superpose eq6156 eq10
    | exact resolve eq10 eq6156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6156
  have eq6224 : y = (M.op x x) := by
    first
    | (have i₁ := eq6167
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6167
    | exact resolve eq6167 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6167
  have eq6426 : x = (M.op x y) := by
    first
    | (have i₁ := eq110 x
       have i₂ := eq6224
       grind)
    | exact superpose eq6224 eq110
    | exact resolve eq110 eq6224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq6224
  have eq6757 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6159
       grind)
    | exact superpose eq6159 eq16
    | exact resolve eq16 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6159
  have eq6810 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq6757
       have i₂ := eq6426
       grind)
    | exact superpose eq6426 eq6757
    | exact resolve eq6757 eq6426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6426 eq6757
  have eq6811 : False := by grind
  exact eq6811

/-- `Equation860`: `x = x ◇ ((y ◇ z) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxy_pyy_pxy_pyy_pxy_Equation860 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law860 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law860.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq57 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq69 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq55 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq55 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq165 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq69 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq170 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq165 X0 X1
       have j1 := eq57 X0 X1
       grind)
    | (have r₁ := eq165 X0 X1
       have r₂ := eq57 X0 X1
       grind)
    | (have r₁ := eq165 X0 X0
       have r₂ := eq57 X0 X0
       grind)
    | exact resolve eq165 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq165
  have eq457 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq464 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq457 X0 X1
       have i₂ := eq170 X0 X1
       grind)
    | exact superpose eq170 eq457
    | exact resolve eq457 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq457
  have eq467 : False := by grind
  exact eq467
