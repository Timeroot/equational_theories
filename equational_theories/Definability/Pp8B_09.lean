import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_Equation1483 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq263 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq82 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq82 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq271 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq263 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq272 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq271 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq274 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq272
    | (have j0 := eq272 X0 X1
       grind)
    | exact resolve eq272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq278 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       have j1 := eq270 X0 X1
       grind)
    | (have r₁ := eq274 X0 X1
       have r₂ := eq270 X0 X1
       grind)
    | (have r₁ := eq274 (k X0 X1) X0
       have r₂ := eq270 X0 X1
       grind)
    | (have r₁ := eq274 X0 X0
       have r₂ := eq270 X0 X0
       grind)
    | exact resolve eq274 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq274
  have eq785 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq278 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq278
    | exact resolve eq278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq793 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq278 x y
       grind)
    | exact superpose eq278 eq16
    | (have j1 := eq278 x y
       grind)
    | exact resolve eq16 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq818 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq785 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq785
    | (have j0 := eq785 X0 X1
       grind)
    | exact resolve eq785 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq785
  have eq824 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq818 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq818
    | exact resolve eq818 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq957 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq824 (τ X0) X1
       grind)
    | exact superpose eq824 eq18
    | (have j1 := eq824 (τ X0) X1
       grind)
    | exact resolve eq18 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq824
  have eq1247 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq957 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq957
    | exact resolve eq957 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1295 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1247 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1247
    | (have j0 := eq1247 X0 X1
       grind)
    | exact resolve eq1247 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq1403 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq793
       have i₂ := eq1295 x y
       grind)
    | exact superpose eq1295 eq793
    | (have j1 := eq1295 (σ x) (σ y)
       grind)
    | (have r₁ := eq793
       have r₂ := eq1295 x y
       grind)
    | exact resolve eq793 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1404 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1403
  have eq1459 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1404
  have eq1483 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq793
       have i₂ := eq1459
       grind)
    | exact superpose eq1459 eq793
    | exact resolve eq793 eq1459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq1459
  have eq1484 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1483
  have eq1485 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1484
  have eq1564 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1485
  have eq1590 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1564
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1564
    | exact resolve eq1564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1596 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1590
       grind)
    | exact superpose eq1590 eq16
    | exact resolve eq16 eq1590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1590
  have eq1715 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1596
       have i₂ := eq1295 x y
       grind)
    | exact superpose eq1295 eq1596
    | (have j1 := eq1295 x y
       grind)
    | (have r₁ := eq1596
       have r₂ := eq1295 x y
       grind)
    | exact resolve eq1596 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq1716 : x = (M.op y y) := by grind
  clear eq1715
  have eq1721 : (M.op x y) = (k x y) := by grind
  clear eq1716
  have eq1750 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1596
       have i₂ := eq1721
       grind)
    | exact superpose eq1721 eq1596
    | exact resolve eq1596 eq1721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596 eq1721
  have eq1753 : False := by grind
  exact eq1753

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation1483 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
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
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X0) (M.op X0 (M.op X1 x))
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  clear eq23
  have eq70 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op X0 (M.op (M.op X0 X2) X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq63 X0 (M.op x X2) (M.op X0 X2)
       have i₂ := eq63 X2 x X0
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq371 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) := by
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
  have eq374 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq768 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq366 x y
       grind)
    | exact superpose eq366 eq16
    | (have j1 := eq366 x y
       grind)
    | exact resolve eq16 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq66 x
       have i₂ := eq366 x x
       grind)
    | exact superpose eq366 eq66
    | (have j1 := eq366 X0 X0
       grind)
    | exact resolve eq66 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq792 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq366 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq793 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq366 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq793 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq797 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq769 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq800 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ (k X0 X0)) (σ X0))) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq797 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq797
    | (have j0 := eq797 X0
       grind)
    | exact resolve eq797 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq3197 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq374 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq374
    | exact resolve eq374 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3241 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3197 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3197
    | (have j0 := eq3197 X0 X1
       grind)
    | exact resolve eq3197 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3197
  have eq3550 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq371 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq371
    | exact resolve eq371 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq3634 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3550 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq3550
    | (have j0 := eq3550 X0 X1
       grind)
    | exact resolve eq3550 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3550
  have eq3666 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (σ (k (τ (M.op X0 X1)) X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (k X0 X1) X2
       have i₂ := eq3634 X0 X1
       grind)
    | exact superpose eq3634 eq18
    | (have j1 := eq3634 X0 X1
       grind)
    | exact resolve eq18 eq3634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3634
  have eq3774 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (k (M.op X0 X1) (σ X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3666 X0 X1 X2
       have i₂ := eq18 (M.op X0 X1) X2
       grind)
    | exact superpose eq18 eq3666
    | (have j0 := eq3666 X0 X1 X2
       grind)
    | exact resolve eq3666 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3666
  have eq3828 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (τ (M.op (σ (k X0 X0)) (σ X0))) = (k (k X0 X0) X0) := by
    intro X0
    grind
  clear eq800
  have eq3830 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (τ (M.op (σ (k X0 X0)) (σ X0))) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq3828 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq3828
    | (have j0 := eq3828 X0
       grind)
    | exact resolve eq3828 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3828
  have eq10548 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq768
       have i₂ := eq3241 x y
       grind)
    | exact superpose eq3241 eq768
    | (have j1 := eq3241 (σ x) (σ y)
       grind)
    | (have r₁ := eq768
       have r₂ := eq3241 x y
       grind)
    | exact resolve eq768 eq3241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq10549 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq10548
  have eq14159 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = (τ (M.op (σ (k X0 X0)) (σ X0))) ∨ (τ (M.op (σ (k X0 X0)) (σ X0))) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq3830 X0
       grind)
    | exact superpose eq3830 eq66
    | (have j1 := eq3830 X0
       grind)
    | exact resolve eq66 eq3830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq3830
  have eq14251 : ∀ X0 : G, (τ (M.op (σ (k X0 X0)) (σ X0))) = (k (k X0 X0) X0) ∨ (τ (M.op (σ (k X0 X0)) (σ X0))) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14159 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq14159
    | (have j0 := eq14159 X0
       grind)
    | exact resolve eq14159 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14159
  have eq14252 : ∀ X0 : G, (τ (M.op (σ (k X0 X0)) (σ X0))) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq14251 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14251
  have eq14272 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14252 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq14252
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq14252 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14295 : ∀ X0 : G, (k (k (τ X0) (τ X0)) (τ X0)) = (τ (M.op (k X0 (σ (τ X0))) (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq14252 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq14252
    | exact resolve eq14252 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14341 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ (k X0 X0)) (σ X0))
       have i₂ := eq14252 X0
       grind)
    | exact superpose eq14252 eq11
    | exact resolve eq11 eq14252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14405 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14272 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14272
  have eq14417 : ∀ X0 : G, (k (k (τ X0) (τ X0)) (τ X0)) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14295 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14295
    | exact resolve eq14295 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14295
  have eq14430 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq14405
  have eq14441 : ∀ X0 : G, (k (τ (k X0 X0)) (τ X0)) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14417 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq14417
    | exact resolve eq14417 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14417
  have eq14460 : ∀ X0 : G, (τ (k (k X0 X0) X0)) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14441 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq14441
    | exact resolve eq14441 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14441
  have eq14532 : ∀ X0 : G, (k (k X0 X0) X0) = (σ (τ (M.op (k X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k (k X0 X0) X0)
       have i₂ := eq14460 X0
       grind)
    | exact superpose eq14460 eq11
    | exact resolve eq11 eq14460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14655 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14532 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq14532
    | exact resolve eq14532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14532
  have eq14736 : ∀ X0 : G, (k (τ (k X0 X0)) (τ X0)) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq14655 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq14655
    | exact resolve eq14655 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14756 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3774 (σ X0) (σ X0) X0
       have i₂ := eq14655 (σ X0)
       grind)
    | exact superpose eq14655 eq3774
    | (have j0 := eq3774 (σ X0) (σ X0) x
       grind)
    | exact resolve eq3774 eq14655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3774
  have eq14805 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq14756 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14756
  have eq14851 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14805 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq14805
    | (have j0 := eq14805 X0
       grind)
    | exact resolve eq14805 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14805
  have eq14868 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14736 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq14736
    | exact resolve eq14736 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14736
  have eq14911 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14851 X0
       have i₂ := eq14341 X0
       grind)
    | exact superpose eq14341 eq14851
    | (have j0 := eq14851 X0
       grind)
    | exact resolve eq14851 eq14341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14851
  have eq14923 : ∀ X0 : G, (M.op (τ (k X0 X0)) (τ X0)) = (τ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14868 X0
       have i₂ := eq14460 X0
       grind)
    | exact superpose eq14460 eq14868
    | exact resolve eq14868 eq14460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14460 eq14868
  have eq14960 : ∀ X0 : G, (k (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14911 X0
       have i₂ := eq14655 X0
       grind)
    | exact superpose eq14655 eq14911
    | (have j0 := eq14911 X0
       grind)
    | exact resolve eq14911 eq14655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14911
  have eq14990 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq14960
  have eq15014 : ∀ X0 : G, (σ (k (σ (k X0 X0)) (σ X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq14341 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq14341
    | exact resolve eq14341 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14341
  have eq15199 : ∀ X0 : G, (σ (σ (k (k X0 X0) X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15014 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq15014
    | exact resolve eq15014 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15014
  have eq15231 : ∀ X0 : G, (σ (σ (M.op (k X0 X0) X0))) = (M.op (σ (σ (k X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15199 X0
       have i₂ := eq14655 X0
       grind)
    | exact superpose eq14655 eq15199
    | exact resolve eq15199 eq14655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15199
  have eq18181 : ∀ X0 : G, (M.op (σ (σ (k (τ X0) (τ X0)))) (σ X0)) = (σ (σ (M.op (k (τ X0) (τ X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq15231 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15231
    | exact resolve eq15231 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15231
  have eq18278 : ∀ X0 : G, (σ (σ (M.op (τ (k X0 X0)) (τ X0)))) = (M.op (σ (σ (τ (k X0 X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq18181 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq18181
    | exact resolve eq18181 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18181
  have eq18310 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (σ (M.op (τ (k X0 X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18278 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq18278
    | exact resolve eq18278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18278
  have eq18336 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (σ (τ (M.op (k X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq18310 X0
       have i₂ := eq14923 X0
       grind)
    | exact superpose eq14923 eq18310
    | exact resolve eq18310 eq14923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18310
  have eq18355 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq18336 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq18336
    | exact resolve eq18336 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18336
  have eq22415 : ∀ X0 : G, (M.op (M.op (τ X0) (τ X0)) (τ X0)) = (τ (M.op (k X0 (σ (τ X0))) (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq14430 (τ X0)
       have i₂ := eq374 X0 (τ X0)
       grind)
    | exact superpose eq374 eq14430
    | (have j0 := eq14430 (τ X0)
       have j1 := eq374 X0 (τ X0)
       grind)
    | exact resolve eq14430 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374 eq14430
  have eq22521 : ∀ X0 : G, (M.op (M.op (τ X0) (τ X0)) (τ X0)) = (τ (M.op (k X0 (σ (τ X0))) (σ (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq22415 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22415
  have eq22537 : ∀ X0 : G, (M.op (M.op (τ X0) (τ X0)) (τ X0)) = (τ (M.op (k X0 X0) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq22521 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22521
    | (have j0 := eq22521 X0
       grind)
    | exact resolve eq22521 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22521
  have eq49624 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ (M.op (k X0 X0) X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq70 (τ X0) (τ X0)
       have i₂ := eq22537 X0
       grind)
    | exact superpose eq22537 eq70
    | (have j1 := eq22537 X0
       grind)
    | exact resolve eq70 eq22537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq22537
  have eq49848 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (k X0 X0) X0)) (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0) (σ X0) (σ X0)
       have i₂ := eq14990 X0
       grind)
    | exact superpose eq14990 eq63
    | (have j1 := eq14990 X0
       grind)
    | exact resolve eq63 eq14990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14990
  have eq51542 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (τ (M.op (k (σ X0) (σ X0)) (σ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49624 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49624
    | exact resolve eq49624 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49624
  have eq51687 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (τ (M.op (σ (k X0 X0)) (σ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51542 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq51542
    | (have j0 := eq51542 X0
       grind)
    | exact resolve eq51542 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51542
  have eq51713 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51687 X0
       have i₂ := eq14252 X0
       grind)
    | exact superpose eq14252 eq51687
    | (have j0 := eq51687 X0
       grind)
    | exact resolve eq51687 eq14252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14252 eq51687
  have eq51729 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51713 X0
       have i₂ := eq14655 X0
       grind)
    | exact superpose eq14655 eq51713
    | (have j0 := eq51713 X0
       grind)
    | exact resolve eq51713 eq14655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14655 eq51713
  have eq57558 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (k X0 X0) X0)) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq49848 x
       have i₂ := eq366 x x
       grind)
    | exact superpose eq366 eq49848
    | (have j0 := eq49848 X0
       have j1 := eq366 X0 X0
       grind)
    | exact resolve eq49848 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq49848
  have eq57626 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (k X0 X0) X0)) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq57558 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57558
  have eq57634 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (k X0 X0) X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq57626 X0
       have j1 := eq794 X0
       grind)
    | (have r₁ := eq57626 X0
       have r₂ := eq794 X0
       grind)
    | exact resolve eq57626 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794 eq57626
  have eq57724 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (M.op (k (τ X0) (τ X0)) (τ X0))) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq57634 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq57634
    | (have j0 := eq57634 (τ X0)
       grind)
    | exact resolve eq57634 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq57634
  have eq57826 : ∀ X0 : G, (M.op (σ (M.op (k (τ X0) (τ X0)) (τ X0))) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq57724 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57724
    | (have j0 := eq57724 X0
       grind)
    | exact resolve eq57724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57724
  have eq57860 : ∀ X0 : G, (M.op (σ (M.op (τ (k X0 X0)) (τ X0))) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq57826 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq57826
    | (have j0 := eq57826 X0
       grind)
    | exact resolve eq57826 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq57826
  have eq57883 : ∀ X0 : G, (M.op (σ (τ (M.op (k X0 X0) X0))) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq57860 X0
       have i₂ := eq14923 X0
       grind)
    | exact superpose eq14923 eq57860
    | (have j0 := eq57860 X0
       grind)
    | exact resolve eq57860 eq14923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14923 eq57860
  have eq57899 : ∀ X0 : G, (M.op (M.op (k X0 X0) X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq57883 X0
       have i₂ := eq11 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq11 eq57883
    | (have j0 := eq57883 X0
       grind)
    | exact resolve eq57883 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57883
  have eq57915 : ∀ X0 : G, (M.op (M.op (k X0 X0) X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57899 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57899
    | (have j0 := eq57899 X0
       grind)
    | exact resolve eq57899 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57899
  have eq57964 : ∀ X0 : G, (k X0 X0) = (M.op X0 (M.op (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 X0 (k X0 X0) (k X0 X0)
       have i₂ := eq57915 X0
       grind)
    | exact superpose eq57915 eq63
    | (have j1 := eq57915 X0
       grind)
    | exact resolve eq63 eq57915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq57915
  have eq58054 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51729 X0
       have i₂ := eq57964 X0
       grind)
    | exact superpose eq57964 eq51729
    | (have j0 := eq51729 X0
       have j1 := eq57964 X0
       grind)
    | exact resolve eq51729 eq57964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51729 eq57964
  have eq58170 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq58054 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58054
  have eq58461 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq58170 (σ X0)
       grind)
    | exact superpose eq58170 eq15
    | (have j1 := eq58170 (σ X0)
       grind)
    | exact resolve eq15 eq58170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58170
  have eq58834 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq58461
  have eq58914 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58834 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq58834
    | (have j0 := eq58834 X0
       grind)
    | exact resolve eq58834 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58834
  have eq58915 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq58914 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58914
  have eq58979 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq58915 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58915
    | exact resolve eq58915 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59322 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq58979 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq58979
    | exact resolve eq58979 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq58979
  have eq59412 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq59322 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59322
    | exact resolve eq59322 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59322
  have eq59656 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq18355 X0
       have i₂ := eq59412 X0
       grind)
    | exact superpose eq59412 eq18355
    | exact resolve eq18355 eq59412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18355
  have eq704048 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq10549
       grind)
    | exact superpose eq10549 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq10549
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq10549
       grind)
    | exact resolve eq13 eq10549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10549
  have eq704132 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq704048
  have eq704133 : x = (M.op y y) ∨ y = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq704132
  have eq704212 : (σ x) = (σ (k y y)) ∨ x = (M.op y y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq704133
       have i₂ := eq58915 y
       grind)
    | exact superpose eq58915 eq704133
    | exact resolve eq704133 eq58915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704133
  have eq704291 : y = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq704212
       have i₂ := eq59412 y
       grind)
    | exact superpose eq59412 eq704212
    | exact resolve eq704212 eq59412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704212
  have eq704316 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq792 x y
       have i₂ := eq704291
       grind)
    | exact superpose eq704291 eq792
    | (have j0 := eq792 x y
       grind)
    | exact resolve eq792 eq704291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792 eq704291
  have eq704406 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq704316
  have eq704407 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq704406
  have eq704417 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq704407
       have i₂ := eq58915 y
       grind)
    | exact superpose eq58915 eq704407
    | exact resolve eq704407 eq58915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704407
  have eq704425 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq704417
       have i₂ := eq59412 y
       grind)
    | exact superpose eq59412 eq704417
    | exact resolve eq704417 eq59412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704417
  have eq704426 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq704425
  have eq704437 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq704426
       grind)
    | exact superpose eq704426 eq16
    | exact resolve eq16 eq704426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704501 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq704426
       grind)
    | exact superpose eq704426 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq704426
       grind)
    | exact resolve eq13 eq704426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704426
  have eq704585 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq704501
  have eq704617 : (σ x) = (σ (k y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq704585
       have i₂ := eq58915 y
       grind)
    | exact superpose eq58915 eq704585
    | exact resolve eq704585 eq58915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58915 eq704585
  have eq704676 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq704617
       have i₂ := eq59412 y
       grind)
    | exact superpose eq59412 eq704617
    | exact resolve eq704617 eq59412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59412 eq704617
  have eq704677 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq704676
  have eq704697 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq704677
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq704677
    | exact resolve eq704677 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704677
  have eq704725 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3241 x y
       have i₂ := eq704697
       grind)
    | exact superpose eq704697 eq3241
    | (have j0 := eq3241 x y
       grind)
    | exact resolve eq3241 eq704697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3241 eq704697
  have eq705124 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq704725
  have eq705362 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq705124
       have r₂ := eq704437
       grind)
    | exact resolve eq705124 eq704437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705124
  have eq705683 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq704437
       have i₂ := eq705362
       grind)
    | exact superpose eq705362 eq704437
    | exact resolve eq704437 eq705362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704437 eq705362
  have eq705772 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq705683
  have eq705773 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq705772
  have eq706014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq59656 y
       have i₂ := eq705773
       grind)
    | exact superpose eq705773 eq59656
    | exact resolve eq59656 eq705773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705773
  have eq706321 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq706014
       have r₂ := eq16
       grind)
    | exact resolve eq706014 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706014
  have eq706615 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq706321
       grind)
    | exact superpose eq706321 eq10
    | exact resolve eq10 eq706321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706321
  have eq707261 : x = (M.op y y) := by
    first
    | (have i₁ := eq706615
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq706615
    | exact resolve eq706615 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706615
  have eq707883 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59656 y
       have i₂ := eq707261
       grind)
    | exact superpose eq707261 eq59656
    | exact resolve eq59656 eq707261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59656 eq707261
  have eq708192 : False := by grind
  exact eq708192

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation1483 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq57
  have eq81 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq66 X1
       grind)
    | exact superpose eq66 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq87
  have eq270 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq280 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq270 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq284 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq280 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq280 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq280 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq294 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq284 X0 X1
       have j1 := eq81 X1 (σ X0)
       grind)
    | (have r₁ := eq284 X0 X0
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq284 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq284
  have eq301 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq294
    | (have j0 := eq294 X0 X1
       grind)
    | exact resolve eq294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq302 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq301 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq308 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq302 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq302
    | exact resolve eq302 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq302 x y
       grind)
    | exact superpose eq302 eq16
    | exact resolve eq16 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq405 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq308 X0 (τ X1)
       grind)
    | exact superpose eq308 eq18
    | exact resolve eq18 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq308
  have eq424 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq405 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq405
    | exact resolve eq405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq433 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq424 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq424
    | exact resolve eq424 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq454 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq319
       have i₂ := eq433 x y
       grind)
    | exact superpose eq433 eq319
    | exact resolve eq319 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq433
  have eq455 : False := by grind
  exact eq455

/-- `Equation1484`: `x = (y ◇ x) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_pxx_pyx_Equation1484 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1484 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1484.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq70
    | (have j0 := eq70 (σ y) (σ X0)
       grind)
    | exact resolve eq70 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq70 y x
       grind)
    | exact superpose eq70 eq76
    | (have j1 := eq70 y x
       grind)
    | exact resolve eq76 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq116 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq117 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq99 eq70
    | (have j0 := eq70 (σ y) (σ x)
       grind)
    | exact resolve eq70 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq130 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq149 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq138 eq16
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq223 : y = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq228 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq127 eq51
    | exact resolve eq51 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq234 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq228
    | (have j0 := eq228 (σ x)
       grind)
    | exact resolve eq228 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq234
    | exact resolve eq234 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq244 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq239
  have eq254 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq244 eq228
    | exact resolve eq228 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq244
  have eq261 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq254
  have eq276 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq261 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq261
       grind)
    | exact resolve eq13 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq276
  have eq431 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq117
    | (have r₁ := eq117
       have r₂ := eq127
       grind)
    | exact resolve eq117 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq127
  have eq432 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq431
  have eq856 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq432 eq99
    | exact resolve eq99 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq859 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq856
  have eq868 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq859 eq261
    | exact resolve eq261 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq859
  have eq895 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq868
  have eq900 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq895
       have r₂ := eq130
       grind)
    | exact resolve eq895 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq904 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq900 eq29
    | exact resolve eq29 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq911 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq900 eq99
    | exact resolve eq99 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq915 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq900 eq130
    | exact resolve eq130 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq929 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq900 eq279
    | exact resolve eq279 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq900
  have eq943 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq929
  have eq955 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by grind
  clear eq915
  have eq958 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq911
  have eq966 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq904
    | exact resolve eq904 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq904
  have eq974 : y ≠ y ∨ x = y ∨ (k y x) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq966 eq116
    | (have r₁ := eq116
       have r₂ := eq966
       grind)
    | exact resolve eq116 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq966
  have eq980 : y ≠ y ∨ x = y ∨ (k y x) = (M.op y y) := by grind
  clear eq974
  have eq981 : x = y ∨ (k y x) = (M.op y y) := by grind
  clear eq980
  have eq1115 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq958 eq943
    | exact resolve eq943 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943 eq958
  have eq1118 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1115
  have eq1121 : y = (M.op x y) := by
    first
    | (have r₁ := eq1118
       have r₂ := eq955
       grind)
    | exact resolve eq1118 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq1118
  have eq1123 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1121 eq20
    | exact resolve eq20 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1127 : x ≠ y ∨ y = (k y x) := by
    first
    | exact superpose eq1121 eq66
    | exact resolve eq66 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1133 : y = (M.op y (M.op y y)) := by
    first
    | exact superpose eq1121 eq223
    | exact resolve eq223 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq1141 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1123
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1123
    | exact resolve eq1123 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1177 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1141 eq26
    | exact resolve eq26 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1278 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq1133
       grind)
    | exact superpose eq1133 eq50
    | exact resolve eq50 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1133
  have eq1291 : y = (M.op y y) := by
    first
    | exact superpose eq1121 eq1278
    | exact resolve eq1278 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq2410 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq1141 eq86
    | (have j0 := eq86 X0
       grind)
    | exact resolve eq86 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq2411 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1141 eq2410
    | (have j0 := eq2410 X0
       grind)
    | exact resolve eq2410 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410
  have eq2433 : (σ (k y x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2411 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2411
    | (have j0 := eq2411 x
       grind)
    | exact resolve eq2411 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2411
  have eq2454 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1177 eq2433
    | exact resolve eq2433 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2433
  have eq2468 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2454
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq2454
    | exact resolve eq2454 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq2454
  have eq2478 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1141 eq2468
    | exact resolve eq2468 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2468
  have eq2485 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1177 eq2478
    | exact resolve eq2478 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177 eq2478
  have eq2490 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq2485
       have r₂ := eq27
       grind)
    | exact resolve eq2485 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2485
  have eq2502 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq2490 eq149
    | exact resolve eq149 eq2490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq2490
  have eq2504 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1121 eq2502
    | exact resolve eq2502 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121 eq2502
  have eq2521 : y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq981
       have i₂ := eq1291
       grind)
    | exact superpose eq1291 eq981
    | exact resolve eq981 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981 eq1291
  have eq2522 : y = (k y x) := by
    first
    | (have r₁ := eq2521
       have r₂ := eq1127
       grind)
    | exact resolve eq2521 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127 eq2521
  have eq2523 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2522
       have i₂ := eq2504
       grind)
    | exact superpose eq2504 eq2522
    | exact resolve eq2522 eq2504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504 eq2522
  have eq2526 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2523 eq15
    | exact resolve eq15 eq2523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523
  have eq2541 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2526
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2526
    | exact resolve eq2526 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2526
  have eq2543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1141 eq2541
    | exact resolve eq2541 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141 eq2541
  have eq2545 : False := by grind
  exact eq2545

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyy_pyy_pxy_Equation1485 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq135 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq135 (σ X0)
       grind)
    | exact superpose eq135 eq15
    | exact resolve eq15 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq138 X0
       have i₂ := eq135 X0
       grind)
    | exact superpose eq135 eq138
    | exact resolve eq138 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq138
  have eq881 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq965 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq881 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq2611 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq965 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq2615 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2611 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq2611 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq2611 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq2611 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq2611 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2611
  have eq2668 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq2615 X0 (τ X1)
       grind)
    | exact superpose eq2615 eq19
    | (have j1 := eq2615 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq2615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2673 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2615 (σ X0) (σ X1)
       grind)
    | exact superpose eq2615 eq15
    | (have j1 := eq2615 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq2615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2615
  have eq2779 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2668 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2668
    | exact resolve eq2668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2668
  have eq2840 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2779 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2779
    | (have j0 := eq2779 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq2779 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2779
  have eq3047 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2673 x y
       grind)
    | exact superpose eq2673 eq16
    | (have j1 := eq2673 x y
       grind)
    | exact resolve eq16 eq2673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673
  have eq3307 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3047
       have i₂ := eq2840 y x
       grind)
    | exact superpose eq2840 eq3047
    | (have j1 := eq2840 (σ x) (σ y)
       grind)
    | (have r₁ := eq3047
       have r₂ := eq2840 y x
       grind)
    | (have r₁ := eq3047
       have r₂ := eq2840 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3047
       have r₂ := eq2840 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3047 eq2840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2840 eq3047
  have eq3308 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3307
  have eq3312 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3308
       grind)
    | exact superpose eq3308 eq10
    | exact resolve eq10 eq3308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3308
  have eq3363 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3312
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3312
    | exact resolve eq3312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3312
  have eq3364 : x = y := by grind
  clear eq3363
  have eq3366 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3364
       grind)
    | exact superpose eq3364 eq16
    | exact resolve eq16 eq3364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364
  have eq3367 : False := by grind
  exact eq3367

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_pxy_x_pxy_Equation1485 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq24 eq35
  have eq66 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
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
  have eq71 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq86 x y
       grind)
    | exact superpose eq86 eq44
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq44 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq117
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118 eq86
    | (have j0 := eq86 (σ x) (σ y)
       grind)
    | exact resolve eq86 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq126
       have r₂ := eq27
       grind)
    | exact resolve eq126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq129
    | exact resolve eq129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq145 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq67
    | exact resolve eq67 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq146 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq27
    | exact resolve eq27 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq71
    | (have r₁ := eq71
       have r₂ := eq131
       grind)
    | exact resolve eq71 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq131
  have eq472 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq471
  have eq473 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq472
       have r₂ := eq145
       grind)
    | exact resolve eq472 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq472
  have eq476 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq473 eq118
    | exact resolve eq118 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq473
  have eq480 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq476
  have eq485 : x = (M.op x y) := by
    first
    | (have r₁ := eq480
       have r₂ := eq146
       grind)
    | exact resolve eq480 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq480
  have eq488 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq485 eq20
    | exact resolve eq20 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq492 : x ≠ y ∨ x = (k x y) := by
    first
    | exact superpose eq485 eq66
    | exact resolve eq66 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq493 : x ≠ x ∨ x = y ∨ x = (k x y) := by
    first
    | exact superpose eq485 eq70
    | (have r₁ := eq70
       have r₂ := eq485
       grind)
    | exact resolve eq70 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq485
  have eq498 : x = y ∨ x = (k x y) := by grind
  clear eq493
  have eq504 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq488
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq488
    | exact resolve eq488 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq587 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq504 eq26
    | exact resolve eq26 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq838 : x = (k x y) := by
    first
    | (have r₁ := eq498
       have r₂ := eq492
       grind)
    | exact resolve eq498 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq498
  have eq842 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq838
       grind)
    | exact superpose eq838 eq44
    | exact resolve eq44 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq838
  have eq849 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq504 eq842
    | exact resolve eq842 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq851 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq849
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq849
    | exact resolve eq849 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq849
  have eq852 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq504 eq851
    | exact resolve eq851 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504 eq851
  have eq855 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq852 eq86
    | (have j0 := eq86 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq86 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq852
  have eq856 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq855
  have eq858 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq587 eq856
    | exact resolve eq856 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq856
  have eq861 : False := by grind
  exact eq861

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_y_pxy_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X1))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
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
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq196 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq183
       grind)
    | exact superpose eq183 eq41
    | exact resolve eq41 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq183
  have eq197 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq196
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq196
    | exact resolve eq196 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq196
  have eq199 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq197
    | exact resolve eq197 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq203 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq199 eq184
    | exact resolve eq184 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq203
       have r₂ := eq27
       grind)
    | exact resolve eq203 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq208 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq206 eq27
    | exact resolve eq27 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ x)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq206 eq176
    | exact resolve eq176 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq229 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq217 eq16
    | exact resolve eq16 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq237 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op X0 (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq229 eq16
    | exact resolve eq16 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq237
    | (have j0 := eq237 (σ x)
       grind)
    | exact resolve eq237 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) X1) (M.op X1 X0)) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq237 eq16
    | exact resolve eq16 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq206 eq243
    | exact resolve eq243 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq258 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op X0 (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq252 eq16
    | exact resolve eq16 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq322 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X0)) = X2 ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq247 eq16
    | exact resolve eq16 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq454 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op X0 (σ y)) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq237 eq322
    | exact resolve eq322 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq513 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op X0 (σ y)) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq454 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq661 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : y ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ y = (k x y) := by
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
  have eq703 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq717 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq703
       have i₂ := eq661 sF3
       grind)
    | exact superpose eq661 eq703
    | exact resolve eq703 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq721 : y ≠ (M.op x y) ∨ (k y y) = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq699
       have i₂ := eq661 y
       grind)
    | exact superpose eq661 eq699
    | exact resolve eq699 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq1029 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq229 eq513
    | exact resolve eq513 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq513
  have eq1083 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1029 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1092 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1083 X0
       have i₂ := eq661 sF3
       grind)
    | exact superpose eq661 eq1083
    | exact resolve eq1083 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1747 : (σ x) = (M.op (M.op (σ y) (σ x)) (k (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq258 sF2
       have i₂ := eq661 sF2
       grind)
    | exact superpose eq661 eq258
    | exact resolve eq258 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq1751 : (σ y) = (M.op (M.op (k (σ x) (σ x)) (σ y)) (k (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1092 sF2
       have i₂ := eq661 sF2
       grind)
    | exact superpose eq661 eq1092
    | exact resolve eq1092 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq2743 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (k (σ y) (σ y)) (k (σ x) (σ x)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1751 eq322
    | exact resolve eq322 eq1751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq1751
  have eq2760 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (k (σ y) (σ y)) (k (σ x) (σ x)))) ∨ y = (M.op x y) := by grind
  clear eq2743
  have eq12000 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq206 eq717
    | (have r₁ := eq717
       have r₂ := eq206
       grind)
    | exact resolve eq717 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq717
  have eq12001 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12000
  have eq12002 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq199 eq12001
    | exact resolve eq12001 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12001
  have eq12003 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12002
       have r₂ := eq208
       grind)
    | exact resolve eq12002 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq12002
  have eq12012 : (σ x) = (M.op (k (σ y) (σ y)) (k (σ x) (σ x))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12003 eq1747
    | exact resolve eq1747 eq12003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747 eq12003
  have eq12151 : (σ x) = (M.op (k (σ y) (σ y)) (k (σ x) (σ x))) ∨ y = (M.op x y) := by grind
  clear eq12012
  have eq21076 : (k (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (M.op (k (σ y) (σ y)) (k (σ x) (σ x))) (σ y)) = (k (M.op (k (σ y) (σ y)) (k (σ x) (σ x))) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2760 eq13
    | (have j0 := eq13 (M.op (k (σ y) (σ y)) (k (σ x) (σ x))) (σ y)
       grind)
    | exact resolve eq13 eq2760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2760
  have eq21159 : (M.op (M.op (k (σ y) (σ y)) (k (σ x) (σ x))) (σ y)) = (k (M.op (k (σ y) (σ y)) (k (σ x) (σ x))) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq21076
       have r₂ := eq661 (σ y)
       grind)
    | exact resolve eq21076 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21076
  have eq21180 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12151 eq21159
    | exact resolve eq21159 eq12151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12151 eq21159
  have eq21192 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq21180
    | exact resolve eq21180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq21180
  have eq21199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq199 eq21192
    | exact resolve eq21192 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq21192
  have eq21202 : y = (M.op x y) := by
    first
    | (have r₁ := eq21199
       have r₂ := eq27
       grind)
    | exact resolve eq21199 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21199
  have eq21204 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21202
       grind)
    | exact superpose eq21202 eq18
    | exact resolve eq18 eq21202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq21205 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq21202
       grind)
    | exact superpose eq21202 eq24
    | exact resolve eq24 eq21202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq21210 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq721
       have i₂ := eq21202
       grind)
    | exact superpose eq21202 eq721
    | (have r₁ := eq721
       have r₂ := eq21202
       grind)
    | exact resolve eq721 eq21202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721 eq21202
  have eq21211 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (k x (M.op x y)) := by grind
  clear eq21210
  have eq21213 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21205 eq20
    | exact resolve eq20 eq21205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21205
  have eq23779 : (k (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k x (M.op x y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq21211 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | exact resolve eq13 eq21211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21211
  have eq23809 : (k x (M.op x y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | (have r₁ := eq23779
       have r₂ := eq661 (M.op x y)
       grind)
    | exact resolve eq23779 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq23779
  have eq23819 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq21204 eq23809
    | exact resolve eq23809 eq21204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21204 eq23809
  have eq23820 : (M.op x y) = (k x (M.op x y)) := by grind
  clear eq23819
  have eq23826 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq23820 eq36
    | exact resolve eq36 eq23820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq23820
  have eq23835 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq23826
    | exact resolve eq23826 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq23826
  have eq23838 : (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21213 eq23835
    | exact resolve eq23835 eq21213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23835
  have eq23845 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23838 eq184
    | exact resolve eq184 eq23838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq23838
  have eq23852 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23845
  have eq23856 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq23852 eq27
    | exact resolve eq27 eq23852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq23852
  have eq23862 : False := by grind
  exact eq23862

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_x_pyx_x_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq80 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (k y x) := by
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
  have eq81 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq22 eq36
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq88 y x
       grind)
    | exact superpose eq88 eq94
    | (have j1 := eq88 y x
       grind)
    | exact resolve eq94 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq128 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq126
    | exact resolve eq126 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq129 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq128
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq128
    | exact resolve eq128 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq128
  have eq198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq88
    | (have j0 := eq88 (σ y) (σ x)
       grind)
    | exact resolve eq88 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq198
    | exact resolve eq198 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq202 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq199
       have r₂ := eq27
       grind)
    | exact resolve eq199 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq204 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq202
    | exact resolve eq202 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq206 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq204 eq27
    | exact resolve eq27 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq969 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq204 eq81
    | (have r₁ := eq81
       have r₂ := eq204
       grind)
    | exact resolve eq81 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq970 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq969
  have eq1049 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq970 eq129
    | exact resolve eq129 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq1053 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1049
  have eq1058 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1053
       have r₂ := eq206
       grind)
    | exact resolve eq1053 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq1053
  have eq1061 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1058 eq67
    | exact resolve eq67 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq1058
  have eq1090 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1061
       have r₂ := eq204
       grind)
    | exact resolve eq1061 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq1061
  have eq1117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1090 eq129
    | exact resolve eq129 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1090
  have eq1120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1117
  have eq1124 : y = (M.op x y) := by
    first
    | (have r₁ := eq1120
       have r₂ := eq27
       grind)
    | exact resolve eq1120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1126 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1124 eq20
    | exact resolve eq20 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1130 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq1124 eq80
    | (have r₁ := eq80
       have r₂ := eq1124
       grind)
    | exact resolve eq80 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1135 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq1130
  have eq1141 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1126
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1126
    | exact resolve eq1126 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1310 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1141 eq26
    | exact resolve eq26 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2181 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq1135
       grind)
    | exact superpose eq1135 eq94
    | exact resolve eq94 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq2188 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1141 eq2181
    | exact resolve eq2181 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2181
  have eq2190 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2188
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2188
    | exact resolve eq2188 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188
  have eq2191 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1141 eq2190
    | exact resolve eq2190 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2190
  have eq2194 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2191 eq88
    | (have j0 := eq88 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq88 eq2191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2191
  have eq2195 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq2194
  have eq2197 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1310 eq2195
    | exact resolve eq2195 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195
  have eq2200 : y = (M.op x x) := by
    first
    | (have r₁ := eq2197
       have r₂ := eq27
       grind)
    | exact resolve eq2197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2197
  have eq2210 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq66
       have i₂ := eq2200
       grind)
    | exact superpose eq2200 eq66
    | exact resolve eq66 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq2200
  have eq2241 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq2210
       have r₂ := eq1124
       grind)
    | exact resolve eq2210 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2210
  have eq2244 : y = (k y x) := by
    first
    | exact superpose eq1124 eq2241
    | exact resolve eq2241 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124 eq2241
  have eq2292 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq94
       have i₂ := eq2244
       grind)
    | exact superpose eq2244 eq94
    | exact resolve eq94 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq2244
  have eq2299 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1141 eq2292
    | exact resolve eq2292 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2292
  have eq2301 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq2299
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2299
    | exact resolve eq2299 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2299
  have eq2302 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1141 eq2301
    | exact resolve eq2301 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141 eq2301
  have eq2305 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2302 eq88
    | (have j0 := eq88 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq88 eq2302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq2302
  have eq2306 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq2305
  have eq2308 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1310 eq2306
    | exact resolve eq2306 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310 eq2306
  have eq2311 : False := by grind
  exact eq2311
