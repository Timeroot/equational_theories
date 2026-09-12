import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pxy_pyx_pyy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq61 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
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
  have eq74 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X3 X2 X4 X0
       have i₂ := eq74 X2 X0 X3 X1
       grind)
    | (have i₁ := eq61 X3 X2 X4 X0
       have i₂ := eq74 X2 X0 X1 X3
       grind)
    | exact superpose eq74 eq61
    | exact resolve eq61 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq74
  have eq1314 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1379 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = (M.op X2 (M.op X3 (M.op X4 (M.op X0 X1)))) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq116 X4 X0 X0 X2 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq116 X0 X0 X1 X3 X4
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq116
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq116 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1417 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1314 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq1418 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1417 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1452 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = (M.op X2 (M.op X3 (M.op X4 (M.op X0 X1)))) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq1379 X0 X1 X2 X3 X4
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1379 X0 X1 X2 X3 X4
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1379 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq1509 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1418 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1418 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1418 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1561 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1452 X0 X1 X2 x x
       have i₂ := eq116 x X0 X1 X2 x
       grind)
    | exact superpose eq116 eq1452
    | (have j0 := eq1452 X0 X1 X2 x x
       grind)
    | exact resolve eq1452 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1452
  have eq1701 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1509 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509
  have eq1704 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1701 X0 X1
       have j1 := eq1561 X0 X1 x
       grind)
    | (have r₁ := eq1701 X0 X1
       have r₂ := eq1561 X0 X1 X1
       grind)
    | (have r₁ := eq1701 X1 X0
       have r₂ := eq1561 X0 X1 X0
       grind)
    | exact resolve eq1701 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561 eq1701
  have eq1826 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1704 (σ X1) (σ X0)
       grind)
    | exact superpose eq1704 eq15
    | exact resolve eq15 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1853 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1826 X0 X1
       have i₂ := eq1704 X1 X0
       grind)
    | exact superpose eq1704 eq1826
    | exact resolve eq1826 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704 eq1826
  have eq2080 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1853 x y
       grind)
    | exact superpose eq1853 eq16
    | (have r₁ := eq16
       have r₂ := eq1853 x y
       grind)
    | exact resolve eq16 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq2108 : False := by grind
  exact eq2108

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_y_pyy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq29 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq29
    | (have j0 := eq29 (M.op x y)
       grind)
    | exact resolve eq29 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq38 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq30 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30
    | (have j0 := eq30 x
       grind)
    | exact resolve eq30 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq49 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq53 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 x y X0 X1
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
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
  have eq55 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 y X0 X1 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 y X0 X1 x
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    grind
  have eq59 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ y) X0 X1 (σ x)
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq9
    | (have j0 := eq9 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq84 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X1)) ≠ X0 ∨ (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op X2 (M.op X3 X0))) ∨ (M.op (M.op X2 (M.op X3 X0)) (M.op X2 (M.op X3 X0))) = (k (M.op X0 X1) (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X1) (M.op X2 (M.op X3 X0))
       have i₂ := eq9 X0 X1 X2 X3
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X0 X1) (M.op X2 (M.op X3 X0))
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq68
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq68 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq134 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq133
    | exact resolve eq133 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq138 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq134
    | exact resolve eq134 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq169 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq10
    | exact resolve eq10 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq210 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq169 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq169
    | exact resolve eq169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq239 : ∀ X0 : G, (τ X0) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    grind
  clear eq210
  have eq301 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq39 eq239
    | exact resolve eq239 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq35
       have i₂ := eq107 sF1
       grind)
    | exact superpose eq107 eq35
    | (have j1 := eq107 (σ (M.op x y))
       grind)
    | exact resolve eq35 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq369 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq42
       have i₂ := eq107 sF2
       grind)
    | exact superpose eq107 eq42
    | (have j1 := eq107 (σ x)
       grind)
    | exact resolve eq42 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq415 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq54
    | exact resolve eq54 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq59 eq54
    | exact resolve eq54 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op X2 (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 y X2 X0
       have i₂ := eq416 X0 X1
       grind)
    | (have i₁ := eq54 x y x X0
       have i₂ := eq416 X0 X1
       grind)
    | exact superpose eq416 eq54
    | exact resolve eq54 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54 X3 X2 X4 X0
       have i₂ := eq415 X2 X0 X3 X1
       grind)
    | (have i₁ := eq54 X3 X2 X4 X0
       have i₂ := eq415 X2 X0 X1 X3
       grind)
    | exact superpose eq415 eq54
    | exact resolve eq54 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1482 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq369
       have i₂ := eq107 x
       grind)
    | exact superpose eq107 eq369
    | (have j1 := eq107 (σ x)
       grind)
    | exact resolve eq369 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1483 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq369
       grind)
    | exact superpose eq369 eq10
    | exact resolve eq10 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2419 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op (M.op X0 (M.op X1 (M.op x y))) x) ∨ x = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op X0 (M.op X1 (M.op x y)))) ∨ (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op X0 (M.op X1 (M.op x y)))) = (k x (M.op X0 (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq53 eq97
    | exact resolve eq97 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq2443 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 (M.op x y))) y) ∨ (M.op x y) ≠ (M.op (M.op X0 (M.op X1 (M.op x y))) x) ∨ (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op X0 (M.op X1 (M.op x y)))) = (k x (M.op X0 (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq437 eq2419
    | (have j0 := eq2419 X0 X1
       grind)
    | exact resolve eq2419 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419
  have eq2471 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op (M.op X0 (M.op X1 (M.op x y))) x) ∨ x = (M.op (M.op X0 (M.op X1 (M.op x y))) y) ∨ (M.op (M.op X0 (M.op X1 (M.op x y))) y) = (k x (M.op X0 (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq437 eq2443
    | (have j0 := eq2443 X0 X1
       grind)
    | exact resolve eq2443 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq2443
  have eq12043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq138
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq138
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq138 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq12069 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12043
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12043
    | exact resolve eq12043 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12043
  have eq12072 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq12069
    | exact resolve eq12069 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12069
  have eq12073 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12072
       have r₂ := eq28
       grind)
    | exact resolve eq12072 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12072
  have eq12074 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12073
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12073
    | exact resolve eq12073 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12073
  have eq12075 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq12074 eq59
    | exact resolve eq59 eq12074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq12078 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq12074 eq60
    | exact resolve eq60 eq12074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12074
  have eq12265 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12078 eq12075
    | exact resolve eq12075 eq12078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12075 eq12078
  have eq12303 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq12265
  have eq12323 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12303 eq1483
    | exact resolve eq1483 eq12303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483
  have eq12325 : x = (k (τ (σ y)) x) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12303 eq301
    | exact resolve eq301 eq12303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12303
  have eq12360 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq12323
  have eq12376 : x = (k y x) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40 eq12325
    | exact resolve eq12325 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12325
  have eq12378 : y = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40 eq12360
    | exact resolve eq12360 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12360
  have eq12447 : x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq12376
       grind)
    | exact superpose eq12376 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq12376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12376
  have eq12448 : x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq12447
  have eq12450 : x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12448
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12448
    | exact resolve eq12448 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12448
  have eq12454 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12450
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12450
    | exact resolve eq12450 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12450
  have eq12455 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq12454
  have eq13068 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq55 x X0
       have i₂ := eq12455
       grind)
    | exact superpose eq12455 eq55
    | exact resolve eq55 eq12455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13071 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq53 X0 y
       have i₂ := eq12455
       grind)
    | exact superpose eq12455 eq53
    | exact resolve eq53 eq12455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12455
  have eq13120 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq107 x
       have i₂ := eq12378
       grind)
    | exact superpose eq12378 eq107
    | (have j0 := eq107 x
       grind)
    | exact resolve eq107 eq12378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq13130 : (M.op x y) = (M.op y x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq13120
  have eq13143 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq55 x X0
       have i₂ := eq13130
       grind)
    | exact superpose eq13130 eq55
    | exact resolve eq55 eq13130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13146 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq53 X0 y
       have i₂ := eq13130
       grind)
    | exact superpose eq13130 eq53
    | exact resolve eq53 eq13130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13130
  have eq13309 : x = y ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13071 eq13068
    | exact resolve eq13068 eq13071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13068 eq13071
  have eq13347 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13309
  have eq13368 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x
       have i₂ := eq13347
       grind)
    | exact superpose eq13347 eq53
    | exact resolve eq53 eq13347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13376 : y ≠ y ∨ x = y ∨ y = (k x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq13347
       grind)
    | exact superpose eq13347 eq13
    | exact resolve eq13 eq13347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13347
  have eq13395 : y ≠ y ∨ x = y ∨ y = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq13376
  have eq13396 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq13395
  have eq13408 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13368 x
       have i₂ := eq416 sF0 x
       grind)
    | (have i₁ := eq13368 x
       have i₂ := eq416 sF0 x
       grind)
    | exact superpose eq416 eq13368
    | (have j0 := eq13368 x
       grind)
    | exact resolve eq13368 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13368
  have eq13433 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq369
       have i₂ := eq13396
       grind)
    | exact superpose eq13396 eq369
    | exact resolve eq369 eq13396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13470 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13433
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13433
    | exact resolve eq13433 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13433
  have eq13510 : x ≠ x ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13408 eq13
    | exact resolve eq13 eq13408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13408
  have eq13529 : x ≠ x ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13510
  have eq13530 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13529
  have eq13545 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13530 eq368
    | exact resolve eq368 eq13530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq13581 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13545
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13545
    | exact resolve eq13545 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13545
  have eq28937 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq13470 eq415
    | exact resolve eq415 eq13470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13470
  have eq29179 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq13581 eq9
    | exact resolve eq9 eq13581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29193 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq13581 eq415
    | exact resolve eq415 eq13581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13581
  have eq29260 : (M.op x y) ≠ (M.op y x) ∨ x = (M.op y y) ∨ (k x y) = (M.op y y) := by
    first
    | exact superpose eq55 eq2471
    | exact resolve eq2471 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2471
  have eq39477 : x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq13146 eq13143
    | exact resolve eq13143 eq13146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13143 eq13146
  have eq39550 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq39477
  have eq39625 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq415 x X0 x X1
       have i₂ := eq39550
       grind)
    | exact superpose eq39550 eq415
    | exact resolve eq415 eq39550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq39550
  have eq51494 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op X2 x)) ∨ x = (M.op (M.op x y) (M.op X0 x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 x
       have i₂ := eq39625 X1 X2
       grind)
    | exact superpose eq39625 eq53
    | (have j1 := eq39625 X1 X2
       grind)
    | exact resolve eq53 eq39625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51522 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    grind
  clear eq39625
  have eq65727 : (M.op x y) = (k x (M.op x y)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq58 x x
       have i₂ := eq51522 x x
       grind)
    | exact superpose eq51522 eq58
    | exact resolve eq58 eq51522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq51522
  have eq66101 : (M.op x y) = (k x (M.op x y)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq65727
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq65727
    | exact resolve eq65727 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65727
  have eq248569 : ∀ X0 X2 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ x = (M.op (M.op x y) (M.op X2 x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X2
    first
    | (have i₁ := eq53 X0 x
       have i₂ := eq51494 X2 X0 x
       grind)
    | exact superpose eq51494 eq53
    | (have j1 := eq51494 X2 x X2
       grind)
    | exact resolve eq53 eq51494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51494
  have eq248632 : ∀ X2 : G, x = (M.op (M.op x y) (M.op X2 x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X2
    first
    | (have i₁ := eq248569 x X2
       have i₂ := eq416 sF0 x
       grind)
    | (have i₁ := eq248569 x X2
       have i₂ := eq416 sF0 x
       grind)
    | exact superpose eq416 eq248569
    | (have j0 := eq248569 x X2
       grind)
    | exact resolve eq248569 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248569
  have eq249104 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq248632 eq53
    | exact resolve eq53 eq248632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq248632
  have eq311202 : ∀ X0 X1 : G, (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq28937 eq239
    | (have j1 := eq28937 X0 X1
       grind)
    | exact resolve eq239 eq28937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28937
  have eq311212 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ x = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq39 eq311202
    | (have j0 := eq311202 X0 X1
       grind)
    | exact resolve eq311202 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311202
  have eq320780 : ∀ X0 X1 : G, (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq29193 eq239
    | (have j1 := eq29193 X0 X1
       grind)
    | exact resolve eq239 eq29193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29193
  have eq320790 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq38 eq320780
    | (have j0 := eq320780 X0 X1
       grind)
    | exact resolve eq320780 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320780
  have eq332064 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ x = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq311212 eq60
    | exact resolve eq60 eq311212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311212
  have eq332094 : x = (k x x) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq417 eq332064
    | (have j0 := eq332064 (σ x)
       grind)
    | exact resolve eq332064 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq332064
  have eq332114 : x = y ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13396
       have i₂ := eq332094
       grind)
    | exact superpose eq332094 eq13396
    | exact resolve eq13396 eq332094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13396 eq332094
  have eq332129 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq332114
  have eq332163 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (M.op X2 (σ x)))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq332129 eq564
    | exact resolve eq564 eq332129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq332129
  have eq369087 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X1) (M.op X0 (σ x))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq320790 eq9
    | exact resolve eq9 eq320790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320790
  have eq393780 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4⟩ := hcon
    have f393780_17 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X1) (M.op X0 (σ x))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
      intro X0 X1
      grind
    have f393780_18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
      intro X0 X1 X2 X3
      grind
    have f393780_26 : (M.op x y) ≠ (k (M.op x y) (M.op x y)) := by grind
    have f393780_27 : (σ x) ≠ (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by grind
    have f393780_28 : x ≠ (M.op x y) := by grind
    have f393780_29 : x ≠ y := by grind
    have f393780_30 : (σ x) ≠ (σ y) := by grind
    have f393780_32 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X1) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
      intro X0 X1
      first
      | (have j0 := f393780_17 X0 X1
         grind)
      | (have r₁ := f393780_17 X0 X1
         have r₂ := f393780_26
         grind)
      | exact resolve f393780_17 f393780_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f393780_33 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X1) (M.op X0 (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
      intro X0 X1
      first
      | (have j0 := f393780_32 X0 X1
         grind)
      | (have r₁ := f393780_32 X0 X1
         have r₂ := f393780_28
         grind)
      | exact resolve f393780_32 f393780_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f393780_34 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X1) (M.op X0 (σ x))) ∨ (σ x) = (σ y) := by
      intro X0 X1
      first
      | (have j0 := f393780_33 X0 X1
         grind)
      | (have r₁ := f393780_33 X0 X1
         have r₂ := f393780_29
         grind)
      | exact resolve f393780_33 f393780_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f393780_35 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X1) (M.op X0 (σ x))) := by
      intro X0 X1
      first
      | (have j0 := f393780_34 X0 X1
         grind)
      | (have r₁ := f393780_34 X0 X1
         have r₂ := f393780_30
         grind)
      | exact resolve f393780_34 f393780_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f393780_78 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ (M.op x y))) := by
      intro X0
      first
      | (have i₁ := f393780_18 (σ x) X0 (M.op (σ (M.op x y)) x) x
         have i₂ := f393780_35 x x
         grind)
      | exact superpose f393780_35 f393780_18
      | exact resolve f393780_18 f393780_35
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f393780_170 : (σ x) ≠ (σ x) := by
      first
      | (have i₁ := f393780_27
         have i₂ := f393780_78 (σ y)
         grind)
      | exact superpose f393780_78 f393780_27
      | (have r₁ := f393780_27
         have r₂ := f393780_78 (σ y)
         grind)
      | exact resolve f393780_27 f393780_78
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f393780_176 : False := by grind
    exact f393780_176
  clear eq369087
  have eq393806 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq393780 eq13530
    | exact resolve eq13530 eq393780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393780
  have eq393813 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq393806
  have eq393825 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq393813 eq9
    | exact resolve eq9 eq393813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393813
  have eq393972 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4, g5, g6⟩ := hcon
    have f393972_18 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (M.op X2 (σ x)))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
      intro X0 X1 X2
      grind
    have f393972_19 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
      intro X0 X1
      grind
    have f393972_28 : (M.op X0 (M.op (σ x) (σ y))) ≠ (M.op X0 (σ (M.op x y))) := by grind
    have f393972_32 : x ≠ y := by grind
    have f393972_33 : (σ x) ≠ (σ y) := by grind
    have f393972_34 : x ≠ (M.op x y) := by grind
    have f393972_36 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
      intro X0 X1
      first
      | (have j0 := f393972_19 X0 X1
         grind)
      | (have r₁ := f393972_19 X0 X1
         have r₂ := f393972_32
         grind)
      | exact resolve f393972_19 f393972_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f393972_37 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (M.op X2 (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
      intro X0 X1 X2
      first
      | (have j0 := f393972_18 X0 X1 X2
         grind)
      | (have r₁ := f393972_18 X0 X1 X2
         have r₂ := f393972_34
         grind)
      | exact resolve f393972_18 f393972_34
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f393972_38 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (σ x))) ∨ x = (M.op x y) := by
      intro X0 X1
      first
      | (have j0 := f393972_36 X0 X1
         grind)
      | (have r₁ := f393972_36 X0 X1
         have r₂ := f393972_33
         grind)
      | exact resolve f393972_36 f393972_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f393972_39 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (M.op X2 (σ x)))) ∨ x = y := by
      intro X0 X1 X2
      first
      | (have j0 := f393972_37 X0 X1 X2
         grind)
      | (have r₁ := f393972_37 X0 X1 X2
         have r₂ := f393972_33
         grind)
      | exact resolve f393972_37 f393972_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f393972_40 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op X1 (σ x))) := by
      intro X0 X1
      first
      | (have j0 := f393972_38 X0 X1
         grind)
      | (have r₁ := f393972_38 X0 X1
         have r₂ := f393972_34
         grind)
      | exact resolve f393972_38 f393972_34
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f393972_41 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (M.op X2 (σ x)))) := by
      intro X0 X1 X2
      first
      | (have j0 := f393972_39 X0 X1 X2
         grind)
      | (have r₁ := f393972_39 X0 X1 X2
         have r₂ := f393972_32
         grind)
      | exact resolve f393972_39 f393972_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f393972_88 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) := by
      intro X0
      first
      | (have i₁ := f393972_41 X0 (M.op (σ (M.op x y)) x) x
         have i₂ := f393972_40 x x
         grind)
      | exact superpose f393972_40 f393972_41
      | exact resolve f393972_41 f393972_40
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f393972_433 : (M.op X0 (σ (M.op x y))) ≠ (M.op X0 (σ (M.op x y))) := by
      first
      | (have i₁ := f393972_28
         have i₂ := f393972_88 X0
         grind)
      | exact superpose f393972_88 f393972_28
      | (have r₁ := f393972_28
         have r₂ := f393972_88 X0
         grind)
      | exact resolve f393972_28 f393972_88
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f393972_434 : False := by grind
    exact f393972_434
  clear eq332163 eq393825
  have eq394002 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq393972 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393972
  have eq394032 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X2 (M.op X0 (σ (M.op x y))))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq394002 eq9
    | exact resolve eq9 eq394002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394002
  have eq396289 : ∀ X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X2 (M.op X3 (σ (M.op x y))))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X2 X3
    first
    | exact superpose eq60 eq394032
    | exact resolve eq394032 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq394032
  have eq396396 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq396289 eq29179
    | exact resolve eq29179 eq396289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29179 eq396289
  have eq396454 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq396396
  have eq396488 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq396454
       have r₂ := eq28
       grind)
    | exact resolve eq396454 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396454
  have eq397286 : (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq396488 eq239
    | exact resolve eq239 eq396488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq396488
  have eq397318 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq38 eq397286
    | exact resolve eq397286 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq397286
  have eq397380 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq397318 eq13530
    | exact resolve eq13530 eq397318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13530 eq397318
  have eq397453 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq397380
  have eq397479 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq397453 eq40
    | exact resolve eq40 eq397453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397453
  have eq397552 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39 eq397479
    | exact resolve eq397479 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397479
  have eq397553 : x = (M.op x y) ∨ x = y := by grind
  clear eq397552
  have eq397559 : ∀ X0 X1 : G, y = (M.op (M.op y X0) (M.op X1 x)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq397553 eq55
    | exact resolve eq55 eq397553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq397560 : ∀ X0 : G, x = (M.op (M.op x X0) y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq397553 eq84
    | exact resolve eq84 eq397553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq398020 : x = (k x x) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq397553 eq66101
    | exact resolve eq66101 eq397553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66101
  have eq398587 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq397553 eq249104
    | exact resolve eq249104 eq397553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397553
  have eq398970 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq398587
  have eq399281 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq398020
  have eq400831 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq416 X0 (M.op x x)
       have i₂ := eq397560 x
       grind)
    | exact superpose eq397560 eq416
    | exact resolve eq416 eq397560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq397560
  have eq402039 : x = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq400831 eq249104
    | exact resolve eq249104 eq400831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249104 eq400831
  have eq402256 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq402039
  have eq403692 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12378
       have i₂ := eq399281
       grind)
    | exact superpose eq399281 eq12378
    | exact resolve eq12378 eq399281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12378 eq399281
  have eq404186 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq403692
  have eq410335 : ∀ X0 : G, y = (M.op (M.op y X0) x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq402256 eq397559
    | exact resolve eq397559 eq402256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397559
  have eq410687 : ∀ X0 : G, y = (M.op (M.op y X0) x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq410335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410335
  have eq582438 : y = (M.op (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq410687 x
       have i₂ := eq404186
       grind)
    | exact superpose eq404186 eq410687
    | exact resolve eq410687 eq404186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404186 eq410687
  have eq582482 : y = (M.op (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq582438
  have eq629012 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq582482 eq402256
    | exact resolve eq402256 eq582482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402256 eq582482
  have eq629036 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq629012
  have eq629055 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq398970
       have i₂ := eq629036
       grind)
    | exact superpose eq629036 eq398970
    | exact resolve eq398970 eq629036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398970 eq629036
  have eq629188 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq629055
  have eq629218 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq629188 eq40
    | exact resolve eq40 eq629188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq629188
  have eq629263 : x = y ∨ x = y := by
    first
    | exact superpose eq39 eq629218
    | exact resolve eq629218 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629218
  have eq629264 : x = y := by grind
  clear eq629263
  have eq629268 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq629264
       grind)
    | exact superpose eq629264 eq19
    | exact resolve eq19 eq629264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq629269 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq629264
       grind)
    | exact superpose eq629264 eq25
    | exact resolve eq25 eq629264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq631758 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op y y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq29260
       have i₂ := eq629264
       grind)
    | exact superpose eq629264 eq29260
    | exact resolve eq29260 eq629264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29260
  have eq648563 : x = (M.op x x) ∨ (M.op x y) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq631758
       have i₂ := eq629264
       grind)
    | exact superpose eq629264 eq631758
    | exact resolve eq631758 eq629264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631758
  have eq650300 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq629269
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq629269
    | exact resolve eq629269 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629269
  have eq650303 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1482
       have i₂ := eq629268
       grind)
    | exact superpose eq629268 eq1482
    | exact resolve eq1482 eq629268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482
  have eq654991 : x = (M.op x x) ∨ (k x y) = (M.op y y) := by
    first
    | (have r₁ := eq648563
       have r₂ := eq629268
       grind)
    | exact resolve eq648563 eq629268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648563
  have eq655772 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq650300 eq27
    | exact resolve eq27 eq650300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq650300
  have eq658335 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq650303
    | exact resolve eq650303 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650303
  have eq658458 : x = (M.op x y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq654991
       have i₂ := eq629268
       grind)
    | exact superpose eq629268 eq654991
    | exact resolve eq654991 eq629268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654991
  have eq659262 : x = (k (τ (M.op (σ x) (σ y))) x) := by
    first
    | exact superpose eq655772 eq301
    | exact resolve eq301 eq655772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq659264 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq655772 eq369
    | exact resolve eq369 eq655772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq659590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq655772 eq658335
    | exact resolve eq658335 eq655772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658335
  have eq659644 : (k x x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq658458
       have i₂ := eq629264
       grind)
    | exact superpose eq629264 eq658458
    | exact resolve eq658458 eq629264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629264 eq658458
  have eq660456 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x x)) := by
    first
    | exact superpose eq655772 eq659264
    | exact resolve eq659264 eq655772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659264
  have eq660471 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq659590
       have r₂ := eq28
       grind)
    | exact resolve eq659590 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659590
  have eq660510 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq659644
       have i₂ := eq629268
       grind)
    | exact superpose eq629268 eq659644
    | exact resolve eq659644 eq629268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659644
  have eq660815 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq655772 eq660471
    | exact resolve eq660471 eq655772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655772 eq660471
  have eq660905 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq660815
       have i₂ := eq629268
       grind)
    | exact superpose eq629268 eq660815
    | exact resolve eq660815 eq629268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660815
  have eq660974 : x = (k (M.op x y) x) := by grind
  clear eq629268
  have eq661523 : x = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq660905 eq659262
    | exact resolve eq659262 eq660905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659262 eq660905
  have eq661677 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39 eq661523
    | exact resolve eq661523 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq661523
  have eq664116 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq660510
       have i₂ := eq661677
       grind)
    | exact superpose eq661677 eq660510
    | exact resolve eq660510 eq661677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660510 eq661677
  have eq664169 : x = (M.op x y) := by grind
  clear eq664116
  have eq664213 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq664169 eq21
    | exact resolve eq21 eq664169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq667897 : x = (k x x) := by
    first
    | exact superpose eq664169 eq660974
    | exact resolve eq660974 eq664169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660974 eq664169
  have eq668118 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq660456
       have i₂ := eq667897
       grind)
    | exact superpose eq667897 eq660456
    | exact resolve eq660456 eq667897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660456 eq667897
  have eq668704 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq664213
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq664213
    | exact resolve eq664213 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664213
  have eq668737 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq668118
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq668118
    | exact resolve eq668118 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq668118
  have eq668738 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq668737
  have eq672074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq668704 eq668738
    | exact resolve eq668738 eq668704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668704 eq668738
  have eq673347 : False := by grind
  exact eq673347

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pxx_pxy_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq50 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ X0 ∨ (M.op X2 (M.op X0 (M.op X1 X0))) = (k X2 (M.op X0 (M.op X1 X0))) := by
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
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq76
    | (have j0 := eq76 (σ X0) (σ X1)
       grind)
    | exact resolve eq76 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq76
    | (have j0 := eq76 (σ y) (σ X0)
       grind)
    | exact resolve eq76 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq99 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq76 y x
       grind)
    | exact superpose eq76 eq73
    | (have j1 := eq76 y x
       grind)
    | exact resolve eq73 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq44
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq101 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq76 y y
       grind)
    | exact superpose eq76 eq74
    | (have j1 := eq76 y y
       grind)
    | exact resolve eq74 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq109 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq119 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq159 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq76 (σ X0) sF2
       grind)
    | exact superpose eq76 eq39
    | (have j1 := eq76 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq161 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq130
       have i₂ := eq76 sF0 sF0
       grind)
    | exact superpose eq76 eq130
    | (have j1 := eq76 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq130 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq130 eq16
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op (σ x) (σ y))))) := by
    intro X2 X3
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq14 X0 x X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq387 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 (M.op X2 (M.op X0 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 y X2 X0
       have i₂ := eq386 X0 X1
       grind)
    | (have i₁ := eq52 x y x X0
       have i₂ := eq386 X0 X1
       grind)
    | exact superpose eq386 eq52
    | exact resolve eq52 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
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
  have eq729 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq110 eq76
    | (have j0 := eq76 (σ x) (σ y)
       grind)
    | exact resolve eq76 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq729
    | exact resolve eq729 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq733 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq730
       have r₂ := eq27
       grind)
    | exact resolve eq730 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq735 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq733 eq54
    | exact resolve eq54 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq736 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq733 eq51
    | exact resolve eq51 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq737 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq733 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq733
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq733
       grind)
    | exact resolve eq12 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq733 eq56
    | exact resolve eq56 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq737
  have eq748 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq387 eq736
    | (have j0 := eq736 (σ x)
       grind)
    | exact resolve eq736 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq783 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq92 X0 X0
       grind)
    | exact superpose eq92 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq92 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq92 X0 X0
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq785 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (σ (k X0 X1)) (M.op X2 (M.op X3 (σ X0)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (σ X0) (σ X1) X2 X3
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq14
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq14 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq786 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (M.op (σ X1) X2) (M.op X3 (σ (k X0 X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (σ X1) X2 X3 (σ X0)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq14
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq14 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X1)) = (M.op (σ X0) (M.op X2 (M.op X3 (σ (k X0 X1))))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (σ X0) (σ X1) x x
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq52
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq52 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (σ (k X0 X1))) = (M.op (M.op (M.op X2 (σ (k X0 X1))) X3) (M.op X4 (σ X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (σ X1) X1 (σ X0) X3 X4
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq55
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq55 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq790 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (M.op (σ (k X0 X1)) X2) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (σ X1) (σ X0) X2
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq56
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq56 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq92 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq793 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq783 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq783 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq783 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq805 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq748 eq212
    | exact resolve eq212 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq874 : ∀ X0 X1 X2 X3 X5 : G, (M.op X3 X2) ≠ (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2))) ∨ (M.op X5 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2)))) = (k X5 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq66 (M.op x X0) (M.op (M.op X1 (M.op X2 X0)) X3) X2
       have i₂ := eq55 X0 X1 X2 X3 x
       grind)
    | exact superpose eq55 eq66
    | exact resolve eq66 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq66
  have eq1012 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X5 (M.op X4 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq385 (M.op X4 X2) X3 X0 X5
       have i₂ := eq385 X2 X0 X4 X1
       grind)
    | (have i₁ := eq385 (M.op X4 X2) X3 X0 X5
       have i₂ := eq385 X2 X0 X1 X4
       grind)
    | exact superpose eq385 eq385
    | exact resolve eq385 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1035 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq733 eq385
    | exact resolve eq385 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1369 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq744 eq110
    | exact resolve eq110 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq1372 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1369
  have eq1377 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1372 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1372
       grind)
    | exact resolve eq13 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq1389 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1377 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq1655 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X2 X3))) ≠ (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X3) ∨ (M.op X4 (M.op X0 (M.op X1 (M.op X2 X3)))) = (k X4 (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13 X4 (M.op X0 (M.op X1 (M.op X2 X3)))
       have i₂ := eq674 X1 X2 X3 (M.op X0 (M.op X1 (M.op X2 X3))) X0
       grind)
    | exact superpose eq674 eq13
    | (have j0 := eq13 X4 (M.op X0 (M.op X1 (M.op X2 X3)))
       grind)
    | exact resolve eq13 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1688 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X2 X3))) ≠ (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X3) ∨ (M.op X4 X3) = (k X4 (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1655 X0 X1 X2 X3 X4
       have i₂ := eq674 X1 X2 X3 X4 X0
       grind)
    | exact superpose eq674 eq1655
    | (have j0 := eq1655 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq1655 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655
  have eq1720 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1389 eq110
    | exact resolve eq110 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq1389
  have eq1725 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1720
  have eq1731 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq1725
    | exact resolve eq1725 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725
  have eq1733 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1731
       have r₂ := eq27
       grind)
    | exact resolve eq1731 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731
  have eq1739 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1733 eq805
    | exact resolve eq805 eq1733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1745 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq1733 eq52
    | exact resolve eq52 eq1733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1754 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq1739
  have eq2303 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1754 eq1745
    | exact resolve eq1745 eq1754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745 eq1754
  have eq2338 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq2303 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2303
  have eq2935 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (k X0 x))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq159 eq1035
    | (have j1 := eq159 X0
       grind)
    | exact resolve eq1035 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq4365 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq791 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq791
    | (have j0 := eq791 (τ X0)
       grind)
    | exact resolve eq791 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq4372 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4365 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4365
    | (have j0 := eq4365 X0
       grind)
    | exact resolve eq4365 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4365
  have eq4377 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4372 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4372
    | (have j0 := eq4372 X0
       grind)
    | exact resolve eq4372 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4372
  have eq4464 : ∀ X0 : G, (σ y) = (M.op (σ (k y X0)) (σ x)) ∨ y = (M.op y x) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq94 eq743
    | (have j1 := eq94 X0
       grind)
    | exact resolve eq743 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq743
  have eq5520 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq130 eq785
    | (have j0 := eq785 (M.op x y) (M.op x y) x x
       grind)
    | exact resolve eq785 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq5587 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq20 eq5520
    | (have j0 := eq5520 X0 X1
       grind)
    | exact resolve eq5520 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5520
  have eq5621 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq20 eq5587
    | (have j0 := eq5587 X0 X1
       grind)
    | exact resolve eq5587 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5587
  have eq5784 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (k (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq786 y x X0 X1
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq786
    | (have j0 := eq786 y x x x
       grind)
    | exact resolve eq786 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq5836 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (k (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq5784 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5784
    | (have j0 := eq5784 X0 X1
       grind)
    | exact resolve eq5784 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5784
  have eq5871 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (k (σ y) (σ x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5836 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5836
    | (have j0 := eq5836 X0 X1
       grind)
    | exact resolve eq5836 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5836
  have eq5902 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (k (σ y) (σ x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5871 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5871
    | (have j0 := eq5871 X0 X1
       grind)
    | exact resolve eq5871 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5871
  have eq5924 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (k (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq5902
    | (have j0 := eq5902 X0 X1
       grind)
    | exact resolve eq5902 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5902
  have eq5971 : ∀ X0 : G, (k (σ y) (σ x)) = (M.op (M.op (k (σ y) (σ x)) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq790 y x x
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq790
    | (have j0 := eq790 y x x
       grind)
    | exact resolve eq790 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq6067 : ∀ X0 : G, (k (σ y) (σ x)) = (M.op (M.op (k (σ y) (σ x)) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5971 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5971
    | (have j0 := eq5971 X0
       grind)
    | exact resolve eq5971 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5971
  have eq6101 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (M.op (k (σ y) (σ x)) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq6067 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6067
    | (have j0 := eq6067 X0
       grind)
    | exact resolve eq6067 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6067
  have eq6130 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (M.op (k (σ y) (σ x)) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq6101 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6101
    | (have j0 := eq6101 X0
       grind)
    | exact resolve eq6101 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6101
  have eq6152 : ∀ X0 : G, (k (σ y) (σ x)) = (M.op (M.op (k (σ y) (σ x)) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq6130
    | (have j0 := eq6130 X0
       grind)
    | exact resolve eq6130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6130
  have eq7700 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op (σ x) (M.op X0 (M.op X1 (k (σ x) (σ x))))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq787 x x x x
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq787
    | (have j0 := eq787 x x x x
       grind)
    | exact resolve eq787 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq787
  have eq7772 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op (σ x) (M.op X0 (M.op X1 (k (σ x) (σ x))))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq7700 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7700
    | (have j0 := eq7700 X0 X1
       grind)
    | exact resolve eq7700 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7700
  have eq7807 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op (σ x) (M.op X0 (M.op X1 (k (σ x) (σ x))))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq7772 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7772
    | (have j0 := eq7772 X0 X1
       grind)
    | exact resolve eq7772 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7772
  have eq8643 : ∀ X0 X1 X2 : G, (M.op X0 (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (M.op X0 (k (σ (M.op x y)) (σ (M.op x y)))) X1) (M.op X2 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq130 eq788
    | (have j0 := eq788 (M.op x y) (M.op x y) X2 x x
       grind)
    | exact resolve eq788 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq788
  have eq8791 : ∀ X0 X1 X2 : G, (M.op X0 (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (M.op X0 (k (σ (M.op x y)) (σ (M.op x y)))) X1) (M.op X2 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq20 eq8643
    | (have j0 := eq8643 X0 X1 X2
       grind)
    | exact resolve eq8643 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8643
  have eq8825 : ∀ X0 X1 X2 : G, (M.op X0 (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (M.op X0 (k (σ (M.op x y)) (σ (M.op x y)))) X1) (M.op X2 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq20 eq8791
    | (have j0 := eq8791 X0 X1 X2
       grind)
    | exact resolve eq8791 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8791
  have eq10640 : ∀ X0 X1 X2 X3 X5 : G, (M.op X3 X2) ≠ (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2))) ∨ (M.op X5 X2) = (k X5 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq874 X0 X1 X2 X3 X5
       have i₂ := eq674 X0 X1 X2 X5 (M.op X3 X2)
       grind)
    | exact superpose eq674 eq874
    | (have j0 := eq874 X0 X1 X2 X3 X5
       grind)
    | exact resolve eq874 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq10800 : ∀ X0 X1 X2 X3 X4 : G, (σ x) ≠ (M.op (σ x) (M.op X2 (M.op X3 (M.op X0 (M.op X1 (σ x)))))) ∨ (M.op X4 (M.op X0 (M.op X1 (σ x)))) = (k X4 (M.op (σ x) (M.op X2 (M.op X3 (M.op X0 (M.op X1 (σ x))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq51 eq10640
    | exact resolve eq10640 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10939 : ∀ X0 X1 X2 X5 : G, (M.op X1 (M.op X2 X0)) ≠ (M.op (M.op X1 (M.op X2 X0)) X0) ∨ (M.op X5 (M.op X2 X0)) = (k X5 (M.op (M.op X1 (M.op X2 X0)) X0)) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq10640 (M.op X0 X1) X2 (M.op x X0) x X5
       have i₂ := eq14 X0 X1 X2 x
       grind)
    | exact superpose eq14 eq10640
    | exact resolve eq10640 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10640
  have eq11042 : ∀ X0 X1 X2 X3 X4 : G, (σ x) ≠ (M.op (σ x) (M.op X1 (σ x))) ∨ (M.op X4 (M.op X0 (M.op X1 (σ x)))) = (k X4 (M.op (σ x) (M.op X2 (M.op X3 (M.op X0 (M.op X1 (σ x))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10800 X1 X1 X4 X0 X4
       have i₂ := eq674 X0 X1 (M.op X1 sF2) sF2 X4
       grind)
    | exact superpose eq674 eq10800
    | (have j0 := eq10800 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq10800 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10800
  have eq11157 : ∀ X0 X1 X4 : G, (σ x) ≠ (M.op (σ x) (M.op X1 (σ x))) ∨ (M.op X4 (M.op X0 (M.op X1 (σ x)))) = (k X4 (M.op (σ x) (M.op X1 (σ x)))) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq11042 X1 X1 X4 X0 X4
       have i₂ := eq674 X0 X1 (M.op X1 sF2) sF2 X4
       grind)
    | exact superpose eq674 eq11042
    | (have j0 := eq11042 X0 X1 x x X4
       grind)
    | exact resolve eq11042 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11042
  have eq14452 : (σ y) = (M.op (k (σ y) (σ x)) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4464 x
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq4464
    | (have j0 := eq4464 x
       grind)
    | exact resolve eq4464 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq4464
  have eq14526 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14452
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14452
    | exact resolve eq14452 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14452
  have eq14534 : (σ y) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq14526
    | exact resolve eq14526 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14526
  have eq40105 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (k X0 (σ x))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2935 (τ X0) X1
       have i₂ := eq34 X0 x
       grind)
    | exact superpose eq34 eq2935
    | (have j0 := eq2935 (τ X0) X1
       grind)
    | exact resolve eq2935 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq2935
  have eq40332 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (k X0 (σ x))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq40105 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq40105
    | (have j0 := eq40105 X0 X1
       grind)
    | exact resolve eq40105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40105
  have eq40345 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (k X0 (σ x))) ∨ (σ x) = (M.op (σ x) X0) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq40332 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq40332
    | (have j0 := eq40332 X0 X1
       grind)
    | exact resolve eq40332 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40332
  have eq63219 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq14534 eq6152
    | exact resolve eq6152 eq14534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6152 eq14534
  have eq63329 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq63219
  have eq63339 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq63329 eq81
    | exact resolve eq81 eq63329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63329
  have eq63386 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq733 eq63339
    | exact resolve eq63339 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733 eq63339
  have eq63440 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq63386
  have eq63446 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq63440
    | exact resolve eq63440 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq63440
  have eq63462 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq76 y x
       have i₂ := eq63446
       grind)
    | exact superpose eq63446 eq76
    | (have j0 := eq76 x y
       grind)
    | exact resolve eq76 eq63446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63475 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq63462
  have eq63490 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63475
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq63475
    | exact resolve eq63475 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq63475
  have eq63522 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq63490
       grind)
    | exact superpose eq63490 eq109
    | exact resolve eq109 eq63490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63490
  have eq63550 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq63522
  have eq63562 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63550
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq63550
    | exact resolve eq63550 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63550
  have eq63619 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq63562 eq5924
    | exact resolve eq5924 eq63562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5924 eq63562
  have eq63658 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op X1 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq63619 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63619
  have eq63667 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq387 eq63658
    | (have j0 := eq63658 X0 (σ x)
       grind)
    | exact resolve eq63658 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63658
  have eq66478 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq63667 eq212
    | exact resolve eq212 eq63667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq63667
  have eq164932 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op (σ x) (M.op X1 (M.op X0 (σ y)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq40345 eq7807
    | (have j1 := eq40345 (σ x) X1
       grind)
    | exact resolve eq7807 eq40345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7807 eq40345
  have eq165045 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op (σ x) (M.op X1 (M.op X0 (σ y)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq164932 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164932
  have eq165069 : ∀ X1 : G, (k (σ x) (σ x)) = (M.op (σ x) (M.op X1 (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    intro X1
    first
    | exact superpose eq387 eq165045
    | (have j0 := eq165045 (σ x) X1
       grind)
    | exact resolve eq165045 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165045
  have eq288693 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq165069 eq2338
    | exact resolve eq2338 eq165069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165069
  have eq288811 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq288693
  have eq289223 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq288811 eq805
    | exact resolve eq805 eq288811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq288811
  have eq289306 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq289223
  have eq289945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq289306 eq1733
    | exact resolve eq1733 eq289306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1733 eq289306
  have eq290079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq289945
  have eq290090 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq290079
       have r₂ := eq27
       grind)
    | exact resolve eq290079 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290079
  have eq290408 : (τ (σ (M.op x y))) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq290090 eq49
    | exact resolve eq49 eq290090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq290090
  have eq290474 : (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq290408
    | exact resolve eq290408 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290408
  have eq290477 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq290474
       have i₂ := eq76 x x
       grind)
    | exact superpose eq76 eq290474
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq290474 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq290506 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4377 x
       have i₂ := eq290474
       grind)
    | exact superpose eq290474 eq4377
    | (have j0 := eq4377 x
       grind)
    | exact resolve eq4377 eq290474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290474
  have eq291204 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op X0 (M.op X1 (M.op X2 (M.op x y)))) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq674 X2 x x X0 X1
       have i₂ := eq290477
       grind)
    | exact superpose eq290477 eq674
    | exact resolve eq674 eq290477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq290477
  have eq291234 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq406 eq291204
    | exact resolve eq291204 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq291204
  have eq323963 : (k (σ y) (σ y)) = (σ (M.op y x)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq291234 y
       grind)
    | exact superpose eq291234 eq101
    | exact resolve eq101 eq291234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq291234
  have eq324038 : (k (σ y) (σ y)) = (σ (M.op y x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq323963
  have eq383801 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq324038
       grind)
    | exact superpose eq324038 eq109
    | exact resolve eq109 eq324038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383823 : (τ (k (σ y) (σ y))) = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op y x)
       have i₂ := eq324038
       grind)
    | exact superpose eq324038 eq16
    | exact resolve eq16 eq324038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324038
  have eq384010 : (k y y) = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq86 eq383823
    | exact resolve eq383823 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383823
  have eq384013 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq383801
       have r₂ := eq290506
       grind)
    | exact resolve eq383801 eq290506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290506 eq383801
  have eq385300 : (k y y) = (τ (k (σ y) (σ x))) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq384013 eq86
    | exact resolve eq86 eq384013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq384013
  have eq385376 : (k y x) = (k y y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq81 eq385300
    | exact resolve eq385300 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq385300
  have eq385394 : (k y x) = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq384010
       have i₂ := eq385376
       grind)
    | exact superpose eq385376 eq384010
    | exact resolve eq384010 eq385376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384010 eq385376
  have eq385432 : (k y x) = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq385394
  have eq385464 : (k y x) = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq385432
       have r₂ := eq13 x x
       grind)
    | exact resolve eq385432 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385432
  have eq385909 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq63446
       have i₂ := eq385464
       grind)
    | exact superpose eq385464 eq63446
    | exact resolve eq63446 eq385464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63446 eq385464
  have eq385961 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq385909
  have eq392052 : ∀ X0 X1 X2 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X1 (M.op (σ x) (σ y))) = (M.op X1 (M.op X2 (M.op X0 (σ x)))) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | exact superpose eq1035 eq11157
    | exact resolve eq11157 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035 eq11157
  have eq392063 : ∀ X0 X1 X2 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X1 (M.op (σ x) (σ y))) = (M.op X1 (M.op X2 (M.op X0 (σ x)))) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | exact superpose eq26 eq392052
    | (have j0 := eq392052 X0 X1 X2
       grind)
    | exact resolve eq392052 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392052
  have eq392085 : ∀ X0 X1 X2 : G, (k X1 (M.op (σ x) (σ y))) = (M.op X1 (M.op X2 (M.op X0 (σ x)))) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | (have j0 := eq392063 X0 X1 X2
       grind)
    | (have r₁ := eq392063 X0 X1 X2
       have r₂ := eq385961
       grind)
    | exact resolve eq392063 eq385961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392063
  have eq392095 : ∀ X0 X1 X2 : G, (k X1 (M.op (σ x) (σ y))) = (M.op X1 (M.op X2 (M.op X0 (σ x)))) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | exact superpose eq26 eq392085
    | (have j0 := eq392085 X0 X1 X2
       grind)
    | exact resolve eq392085 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392085
  have eq415081 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq51 eq392095
    | exact resolve eq392095 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq392095
  have eq415535 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq415081 eq4377
    | (have j0 := eq4377 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq4377 eq415081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4377 eq415081
  have eq415556 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq415535
       have r₂ := eq385961
       grind)
    | exact resolve eq415535 eq385961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385961 eq415535
  have eq415578 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq415556 eq735
    | exact resolve eq735 eq415556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq415556
  have eq415687 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq415578
  have eq415867 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq415687 eq2338
    | exact resolve eq2338 eq415687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338 eq415687
  have eq415957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq415867
  have eq416010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq415957
    | exact resolve eq415957 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415957
  have eq416035 : y = (M.op y x) := by
    first
    | (have r₁ := eq416010
       have r₂ := eq27
       grind)
    | exact resolve eq416010 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416010
  have eq416036 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq416035
       grind)
    | exact superpose eq416035 eq109
    | exact resolve eq109 eq416035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq416097 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq50 X0 y
       have i₂ := eq416035
       grind)
    | exact superpose eq416035 eq50
    | exact resolve eq50 eq416035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq416111 : ∀ X0 : G, y = (M.op (M.op y X0) x) := by
    intro X0
    first
    | (have i₁ := eq56 x y x
       have i₂ := eq416035
       grind)
    | exact superpose eq416035 eq56
    | exact resolve eq56 eq416035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq416115 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq385 x X0 X1 y
       have i₂ := eq416035
       grind)
    | exact superpose eq416035 eq385
    | exact resolve eq385 eq416035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq416157 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq416097 x
       have i₂ := eq386 sF0 x
       grind)
    | (have i₁ := eq416097 x
       have i₂ := eq386 sF0 x
       grind)
    | exact superpose eq386 eq416097
    | (have j0 := eq416097 x
       grind)
    | exact resolve eq416097 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416097
  have eq416179 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq416036
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq416036
    | exact resolve eq416036 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416036
  have eq416187 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq416157 eq161
    | exact resolve eq161 eq416157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq416260 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq416187
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq416187
    | exact resolve eq416187 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416187
  have eq416479 : ∀ X0 : G, (M.op y (M.op X0 (σ (M.op x y)))) = (M.op y (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq8825 y x x
       have i₂ := eq416111 (k sF1 sF1)
       grind)
    | exact superpose eq416111 eq8825
    | exact resolve eq8825 eq416111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8825
  have eq418425 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq416260 eq164
    | exact resolve eq164 eq416260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418497 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq418425
    | exact resolve eq418425 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq418425
  have eq588766 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (M.op y (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq416479 eq5621
    | exact resolve eq5621 eq416479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5621 eq416479
  have eq588909 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (M.op y (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq588766
  have eq628413 : (σ (M.op x y)) = (M.op (σ x) (M.op y (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq416260 eq588909
    | exact resolve eq588909 eq416260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588909
  have eq628526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq628413 eq66478
    | exact resolve eq66478 eq628413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66478
  have eq628654 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq628526
  have eq628669 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq628654
       have r₂ := eq27
       grind)
    | exact resolve eq628654 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628654
  have eq628760 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq628669 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq628669
       grind)
    | exact resolve eq13 eq628669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628806 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq628760 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628760
  have eq632808 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq628806 eq164
    | exact resolve eq164 eq628806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq632863 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq628806 eq416260
    | exact resolve eq416260 eq628806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628806
  have eq633425 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq632863
  have eq633631 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq633425 eq628669
    | exact resolve eq628669 eq633425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633425
  have eq633730 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq633631
  have eq635113 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq633730 eq222
    | exact resolve eq222 eq633730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633730
  have eq642317 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq635113 eq387
    | exact resolve eq387 eq635113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644567 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq628669 eq632808
    | exact resolve eq632808 eq628669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628669 eq632808
  have eq644979 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq644567
  have eq644988 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq644979
    | exact resolve eq644979 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq644979
  have eq645027 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq644988 eq418497
    | exact resolve eq418497 eq644988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418497 eq644988
  have eq645122 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq645027
  have eq645245 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq645122 eq27
    | exact resolve eq27 eq645122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645248 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq645122 eq119
    | (have r₁ := eq119
       have r₂ := eq645122
       grind)
    | exact resolve eq119 eq645122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq645251 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq645122 eq222
    | exact resolve eq222 eq645122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq645407 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq645248
  have eq653009 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (σ x))) = (M.op X0 (M.op X1 (M.op X2 (σ y)))) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq645251 eq1012
    | exact resolve eq1012 eq645251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012 eq645251
  have eq653073 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) = (M.op X0 (M.op X3 (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1 X3
    first
    | exact superpose eq387 eq653009
    | (have j0 := eq653009 X0 X1 (σ x) X3
       grind)
    | exact resolve eq653009 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653009
  have eq677588 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq653073 eq628413
    | exact resolve eq628413 eq653073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628413 eq653073
  have eq677650 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq677588 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677588
  have eq753906 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) (M.op X0 (σ y))) ∨ (M.op X1 (M.op X0 (σ y))) = (k X1 (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq635113 eq10939
    | exact resolve eq10939 eq635113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10939 eq635113
  have eq754079 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) (M.op X0 (σ y))) ∨ (M.op X1 (M.op X0 (σ y))) = (k X1 (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq753906 X0 X1
       grind)
    | (have r₁ := eq753906 X0 X1
       have r₂ := eq645245
       grind)
    | exact resolve eq753906 eq645245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753906
  have eq754204 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op X1 (M.op X0 (σ y))) = (k X1 (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq387 eq754079
    | (have j0 := eq754079 (σ x) X1
       grind)
    | exact resolve eq754079 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754079
  have eq754309 : ∀ X1 : G, (σ x) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op X1 (M.op (σ x) (σ y))) = (k X1 (σ x)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq387 eq754204
    | (have j0 := eq754204 (σ x) X1
       grind)
    | exact resolve eq754204 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754204
  have eq779250 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq645407 eq416179
    | exact resolve eq416179 eq645407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645407
  have eq779341 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq779250
  have eq779450 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq779341 eq387
    | exact resolve eq387 eq779341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq779341
  have eq787436 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq642317 eq754309
    | (have j0 := eq754309 X0
       grind)
    | exact resolve eq754309 eq642317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642317
  have eq787438 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq787436 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787436
  have eq787442 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq787438 X0
       grind)
    | (have r₁ := eq787438 X0
       have r₂ := eq645245
       grind)
    | exact resolve eq787438 eq645245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787438
  have eq802638 : ∀ X0 X1 X2 : G, y ≠ (M.op y (M.op X0 (M.op X1 x))) ∨ (M.op X2 x) = (k X2 (M.op y (M.op X0 (M.op X1 x)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1688 y X0 X1 x X2
       have i₂ := eq416111 (M.op X0 (M.op X1 x))
       grind)
    | exact superpose eq416111 eq1688
    | (have j0 := eq1688 y X0 X1 x X2
       grind)
    | exact resolve eq1688 eq416111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688 eq416111
  have eq802907 : ∀ X0 X1 X2 : G, y ≠ (M.op y (M.op X0 y)) ∨ (M.op X2 x) = (k X2 (M.op y (M.op X0 (M.op X1 x)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq802638 X0 X1 X2
       have i₂ := eq416115 X0 X1
       grind)
    | exact superpose eq416115 eq802638
    | (have j0 := eq802638 X0 X1 X2
       grind)
    | exact resolve eq802638 eq416115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802638
  have eq803317 : ∀ X0 X1 X2 : G, y ≠ (M.op y (M.op x y)) ∨ (M.op X2 x) = (k X2 (M.op y (M.op X0 (M.op X1 x)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq802907 X0 X1 X2
       have i₂ := eq386 y X0
       grind)
    | (have i₁ := eq802907 x X1 X2
       have i₂ := eq386 y X1
       grind)
    | exact superpose eq386 eq802907
    | (have j0 := eq802907 x X1 X2
       grind)
    | exact resolve eq802907 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802907
  have eq803662 : ∀ X0 X2 : G, (M.op X2 x) = (k X2 (M.op y (M.op X0 y))) ∨ y ≠ (M.op y (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq803317 X0 x X2
       have i₂ := eq416115 X0 x
       grind)
    | exact superpose eq416115 eq803317
    | exact resolve eq803317 eq416115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416115 eq803317
  have eq803717 : ∀ X2 : G, y ≠ (M.op y (M.op x y)) ∨ (M.op X2 x) = (k X2 (M.op y (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq803662 x X2
       have i₂ := eq386 y x
       grind)
    | (have i₁ := eq803662 x X2
       have i₂ := eq386 y x
       grind)
    | exact superpose eq386 eq803662
    | (have j0 := eq803662 x X2
       grind)
    | exact resolve eq803662 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq803662
  have eq842541 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq779450 eq754309
    | (have j0 := eq754309 X0
       grind)
    | exact resolve eq754309 eq779450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754309 eq779450
  have eq842618 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq842541 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842541
  have eq842666 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq842618 X0
       have j1 := eq787442 X0
       grind)
    | (have r₁ := eq842618 X0
       have r₂ := eq787442 X0
       grind)
    | exact resolve eq842618 eq787442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787442 eq842618
  have eq842727 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq842666
    | (have j0 := eq842666 X0
       grind)
    | exact resolve eq842666 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842666
  have eq842745 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq842727 X0
       grind)
    | (have r₁ := eq842727 X0
       have r₂ := eq645122
       grind)
    | exact resolve eq842727 eq645122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645122 eq842727
  have eq843204 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq842745 eq416179
    | exact resolve eq416179 eq842745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416179 eq842745
  have eq843798 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq843204
  have eq844086 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq843798 eq677650
    | exact resolve eq677650 eq843798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677650 eq843798
  have eq844149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq844086
  have eq844191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq844149
    | exact resolve eq844149 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844149
  have eq844206 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq844191
       have r₂ := eq27
       grind)
    | exact resolve eq844191 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844191
  have eq845641 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq844206 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq844206
       grind)
    | exact resolve eq13 eq844206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq845690 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq845641 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845641
  have eq858977 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq845690 eq416260
    | exact resolve eq416260 eq845690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416260 eq845690
  have eq859666 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq858977
  have eq859842 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq859666 eq844206
    | exact resolve eq844206 eq859666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844206 eq859666
  have eq859951 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq859842
  have eq859969 : x = (M.op x y) := by
    first
    | (have r₁ := eq859951
       have r₂ := eq645245
       grind)
    | exact resolve eq859951 eq645245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645245 eq859951
  have eq859973 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq859969 eq20
    | exact resolve eq20 eq859969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq860319 : x = (M.op x x) := by
    first
    | exact superpose eq859969 eq416157
    | exact resolve eq416157 eq859969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416157
  have eq860450 : ∀ X0 : G, y ≠ (M.op y x) ∨ (M.op X0 x) = (k X0 (M.op y x)) := by
    intro X0
    first
    | exact superpose eq859969 eq803717
    | exact resolve eq803717 eq859969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803717
  have eq860474 : ∀ X0 : G, (M.op X0 x) = (k X0 (M.op y x)) := by
    intro X0
    first
    | (have j0 := eq860450 X0
       grind)
    | (have r₁ := eq860450 X0
       have r₂ := eq416035
       grind)
    | exact resolve eq860450 eq416035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860450
  have eq860644 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq859973
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq859973
    | exact resolve eq859973 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859973
  have eq860645 : ∀ X0 : G, (k X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq860474 X0
       have i₂ := eq416035
       grind)
    | exact superpose eq416035 eq860474
    | exact resolve eq860474 eq416035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860474
  have eq860679 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq860644 eq26
    | exact resolve eq26 eq860644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq876418 : (k (σ (M.op x y)) (σ y)) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq860645 sF0
       grind)
    | exact superpose eq860645 eq129
    | exact resolve eq129 eq860645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq876456 : ∀ X0 : G, (σ y) ≠ (σ (M.op y x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq793 y X0
       have i₂ := eq860645 y
       grind)
    | exact superpose eq860645 eq793
    | (have j0 := eq793 y X0
       grind)
    | exact resolve eq793 eq860645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq860645
  have eq877258 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq876456 X0
       have i₂ := eq416035
       grind)
    | exact superpose eq416035 eq876456
    | (have j0 := eq876456 X0
       grind)
    | exact resolve eq876456 eq416035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416035 eq876456
  have eq877259 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq877258 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877258
  have eq877286 : (σ (M.op x x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq859969 eq876418
    | exact resolve eq876418 eq859969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859969 eq876418
  have eq877619 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq877259 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq877259
    | (have j0 := eq877259 X0
       grind)
    | exact resolve eq877259 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq877259
  have eq877646 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq877286
       have i₂ := eq860319
       grind)
    | exact superpose eq860319 eq877286
    | exact resolve eq877286 eq860319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860319 eq877286
  have eq877904 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq877646
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq877646
    | exact resolve eq877646 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq877646
  have eq878067 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq860644 eq877904
    | exact resolve eq877904 eq860644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860644 eq877904
  have eq932706 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq877619 eq878067
    | exact resolve eq878067 eq877619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877619 eq878067
  have eq933624 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq860679 eq932706
    | exact resolve eq932706 eq860679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860679 eq932706
  have eq933850 : False := by grind
  exact eq933850

/-- `Equation1480`: `x = (y ◇ x) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation1480 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1480 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1480.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq69 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq70 (σ X0)
       grind)
    | exact superpose eq70 eq15
    | exact resolve eq15 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq75
    | exact resolve eq75 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq75
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq103 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq102
    | exact resolve eq102 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq106 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq103
  have eq157 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq159 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq162 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq157
    | (have j0 := eq157 X0 X1
       grind)
    | exact resolve eq157 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq1689 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq159 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq159
    | exact resolve eq159 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq1747 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1689 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1689
    | (have j0 := eq1689 X0 X1
       grind)
    | exact resolve eq1689 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq2547 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq162 x y
       grind)
    | exact superpose eq162 eq16
    | (have j1 := eq162 x y
       grind)
    | exact resolve eq16 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq6425 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2547
       have i₂ := eq1747 y x
       grind)
    | exact superpose eq1747 eq2547
    | (have j1 := eq1747 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq2547
       have r₂ := eq1747 y x
       grind)
    | (have r₁ := eq2547
       have r₂ := eq1747 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2547
       have r₂ := eq1747 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2547 eq1747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747 eq2547
  have eq6426 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq6425
  have eq6428 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6426
       grind)
    | exact superpose eq6426 eq16
    | exact resolve eq16 eq6426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6426
  have eq6429 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6428
       have r₂ := eq82 x
       grind)
    | exact resolve eq6428 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6428
  have eq6435 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq106 x
       have i₂ := eq6429
       grind)
    | exact superpose eq6429 eq106
    | exact resolve eq106 eq6429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6429
  have eq6472 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq6435
       have r₂ := eq16
       grind)
    | exact resolve eq6435 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6435
  have eq6475 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6472
       grind)
    | exact superpose eq6472 eq10
    | exact resolve eq10 eq6472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6472
  have eq6534 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6475
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6475
    | exact resolve eq6475 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6475
  have eq6537 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6534
       grind)
    | exact superpose eq6534 eq16
    | exact resolve eq16 eq6534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6534
  have eq6538 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq6537
       have r₂ := eq82 x
       grind)
    | exact resolve eq6537 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq6537
  have eq6622 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq6538
       grind)
    | exact superpose eq6538 eq10
    | exact resolve eq10 eq6538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6538
  have eq6681 : y = (M.op x x) := by
    first
    | (have i₁ := eq6622
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6622
    | exact resolve eq6622 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6622
  have eq6691 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq106 x
       have i₂ := eq6681
       grind)
    | exact superpose eq6681 eq106
    | exact resolve eq106 eq6681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq6681
  have eq6729 : False := by grind
  exact eq6729

/-- `Equation1480`: `x = (y ◇ x) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxy_pxx_pyx_Equation1480 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1480 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1480.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq43 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 (M.op X0 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
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
  have eq48 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq28
  have eq94 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq127 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k (M.op (M.op X0 X1) X1) (M.op X2 (M.op X0 X1))) = (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) ∨ (M.op (M.op X0 X1) X1) = (M.op X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) X1) (M.op X2 (M.op X0 X1))
       have i₂ := eq43 X1 X2 X0
       grind)
    | exact superpose eq43 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) X1) (M.op X2 (M.op X0 X1))
       grind)
    | exact resolve eq13 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq95 x y
       grind)
    | exact superpose eq95 eq16
    | (have j1 := eq95 x y
       grind)
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq325 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq48 (M.op X0 X0) (M.op (σ X0) (M.op (σ X0) x))
       have i₂ := eq48 X0 x
       grind)
    | exact superpose eq48 eq48
    | exact resolve eq48 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq944 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq94 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq991 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq944 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq944
    | (have j0 := eq944 X0 X1
       grind)
    | exact resolve eq944 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq1078 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq281 (τ X1) (τ X0)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq281
    | (have j0 := eq281 (τ X1) (τ X0)
       grind)
    | exact resolve eq281 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1086 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1078 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1078
    | (have j0 := eq1078 X0 X1
       grind)
    | exact resolve eq1078 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1089 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1086 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1086
    | (have j0 := eq1086 X0 X1
       grind)
    | exact resolve eq1086 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086
  have eq1091 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1089 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1089
    | (have j0 := eq1089 X0 X1
       grind)
    | exact resolve eq1089 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1092 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1091 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1091
    | (have j0 := eq1091 X0 X1
       grind)
    | exact resolve eq1091 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1093 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1092 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1092
    | (have j0 := eq1092 X0 X1
       grind)
    | exact resolve eq1092 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq1094 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1093 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1093
    | (have j0 := eq1093 X0 X1
       grind)
    | exact resolve eq1093 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1263 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq275
       have i₂ := eq991 x y
       grind)
    | exact superpose eq991 eq275
    | (have j1 := eq991 (σ x) (σ y)
       grind)
    | (have r₁ := eq275
       have r₂ := eq991 x y
       grind)
    | (have r₁ := eq275
       have r₂ := eq991 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq275
       have r₂ := eq991 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq275 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq991
  have eq1264 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1263
  have eq7342 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1264
       grind)
    | exact superpose eq1264 eq16
    | exact resolve eq16 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq7343 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7342
       have r₂ := eq22 x
       grind)
    | exact resolve eq7342 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7342
  have eq7496 : ∀ X0 : G, y = (M.op y (M.op y (M.op y X0))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq7343
       grind)
    | exact superpose eq7343 eq9
    | exact resolve eq9 eq7343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7497 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq7343
       grind)
    | exact superpose eq7343 eq9
    | exact resolve eq9 eq7343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10373 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7496 (M.op y x)
       have i₂ := eq7496 x
       grind)
    | exact superpose eq7496 eq7496
    | exact resolve eq7496 eq7496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7496
  have eq10398 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq10373
  have eq10411 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq43 (σ y) x (σ x)
       have i₂ := eq10398
       grind)
    | exact superpose eq10398 eq43
    | exact resolve eq43 eq10398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq10428 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq10411 X0
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq10411
    | exact resolve eq10411 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10411
  have eq11098 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7497 X0
       have i₂ := eq7343
       grind)
    | exact superpose eq7343 eq7497
    | exact resolve eq7497 eq7343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7343 eq7497
  have eq11116 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq11098 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11098
  have eq11419 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10428 (σ y)
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq10428
    | exact resolve eq10428 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11422 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10428 (σ x)
       have i₂ := eq10398
       grind)
    | exact superpose eq10398 eq10428
    | exact resolve eq10428 eq10398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10428
  have eq11446 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq11422
  have eq11450 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq11419
       have i₂ := eq22 (M.op y y)
       grind)
    | exact superpose eq22 eq11419
    | exact resolve eq11419 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11419
  have eq11455 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq47 y X0
       have i₂ := eq11446
       grind)
    | exact superpose eq11446 eq47
    | exact resolve eq47 eq11446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq11446
  have eq11675 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11455 (σ x)
       have i₂ := eq10398
       grind)
    | exact superpose eq10398 eq11455
    | exact resolve eq11455 eq10398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10398 eq11455
  have eq11705 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq11675
  have eq11720 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq11705
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq11705
    | exact resolve eq11705 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11705
  have eq11874 : (σ y) = (M.op (σ (M.op y y)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq325 y
       have i₂ := eq11450
       grind)
    | exact superpose eq11450 eq325
    | exact resolve eq325 eq11450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq11450
  have eq11909 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq11874
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq11874
    | exact resolve eq11874 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11874
  have eq11923 : (σ y) = (σ (M.op (M.op y y) (M.op y y))) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq11909
       have i₂ := eq22 (M.op y y)
       grind)
    | exact superpose eq22 eq11909
    | exact resolve eq11909 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11909
  have eq11924 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by grind
  clear eq11923
  have eq12106 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11924
       grind)
    | exact superpose eq11924 eq10
    | exact resolve eq10 eq11924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11924
  have eq12205 : x = y ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq12106
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12106
    | exact resolve eq12106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12106
  have eq12207 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12205
       grind)
    | exact superpose eq12205 eq16
    | exact resolve eq16 eq12205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12205
  have eq12208 : (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have r₁ := eq12207
       have r₂ := eq22 x
       grind)
    | exact resolve eq12207 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12207
  have eq12388 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq12208
       have i₂ := eq11720
       grind)
    | exact superpose eq11720 eq12208
    | exact resolve eq12208 eq11720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11720
  have eq12403 : (M.op (M.op y y) (M.op y y)) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (M.op y y) (M.op y y))
       have i₂ := eq12208
       grind)
    | exact superpose eq12208 eq10
    | exact resolve eq10 eq12208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12208
  have eq12473 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq12388
  have eq12505 : y = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq12403
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq12403
    | exact resolve eq12403 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12403
  have eq12645 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12473
       grind)
    | exact superpose eq12473 eq10
    | exact resolve eq10 eq12473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12473
  have eq12748 : x = y ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq12645
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12645
    | exact resolve eq12645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12645
  have eq12946 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12748
       grind)
    | exact superpose eq12748 eq16
    | exact resolve eq16 eq12748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12748
  have eq12950 : (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq12946
       have r₂ := eq22 x
       grind)
    | exact resolve eq12946 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12946
  have eq12969 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq12950
       grind)
    | exact superpose eq12950 eq10
    | exact resolve eq10 eq12950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13084 : y = (M.op y y) := by
    first
    | (have i₁ := eq12969
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq12969
    | exact resolve eq12969 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12969
  have eq13363 : ∀ X0 : G, y ≠ (M.op y y) ∨ (k (M.op y y) (M.op X0 y)) = (M.op (M.op y y) (M.op y y)) ∨ (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq127 y y x
       have i₂ := eq13084
       grind)
    | exact superpose eq13084 eq127
    | exact resolve eq127 eq13084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq13373 : ∀ X0 : G, (k (M.op y y) (M.op X0 y)) = (M.op (M.op y y) (M.op y y)) ∨ (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq13363 X0
       grind)
    | (have r₁ := eq13363 X0
       have r₂ := eq13084
       grind)
    | exact resolve eq13363 eq13084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13363
  have eq13393 : ∀ X0 : G, y = (k (M.op y y) (M.op X0 y)) ∨ (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13373 X0
       have i₂ := eq12505
       grind)
    | exact superpose eq12505 eq13373
    | (have j0 := eq13373 X0
       grind)
    | exact resolve eq13373 eq12505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12505 eq13373
  have eq13409 : ∀ X0 : G, y = (k y (M.op X0 y)) ∨ (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13393 X0
       have i₂ := eq13084
       grind)
    | exact superpose eq13084 eq13393
    | (have j0 := eq13393 X0
       grind)
    | exact resolve eq13393 eq13084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13393
  have eq13418 : ∀ X0 : G, y = (k y (M.op X0 y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13409 X0
       have i₂ := eq13084
       grind)
    | exact superpose eq13084 eq13409
    | (have j0 := eq13409 X0
       grind)
    | exact resolve eq13409 eq13084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13084 eq13409
  have eq15646 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13418 (M.op x x)
       have i₂ := eq11116 x
       grind)
    | exact superpose eq11116 eq13418
    | exact resolve eq13418 eq11116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11116 eq13418
  have eq39628 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq15646
       grind)
    | exact superpose eq15646 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq15646
       grind)
    | exact resolve eq13 eq15646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15646
  have eq39641 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y x) := by grind
  clear eq39628
  have eq39642 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y x) := by grind
  clear eq39641
  have eq39649 : (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq39642
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq39642
    | exact resolve eq39642 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39642
  have eq39655 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq39649
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq39649
    | exact resolve eq39649 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39649
  have eq39658 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq39655
       have i₂ := eq12950
       grind)
    | exact superpose eq12950 eq39655
    | exact resolve eq39655 eq12950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39655
  have eq40423 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq281 x y
       have i₂ := eq39658
       grind)
    | exact superpose eq39658 eq281
    | (have j0 := eq281 x y
       grind)
    | (have r₁ := eq281 x y
       have r₂ := eq39658
       grind)
    | exact resolve eq281 eq39658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39658
  have eq40485 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (σ (k y x)) := by grind
  clear eq40423
  have eq40486 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (σ (k y x)) := by grind
  clear eq40485
  have eq40502 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq281 x y
       grind)
    | (have r₁ := eq40486
       have r₂ := eq281 x y
       grind)
    | exact resolve eq40486 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq40486
  have eq40512 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq40502
       grind)
    | exact superpose eq40502 eq16
    | exact resolve eq16 eq40502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40525 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq40502
       grind)
    | exact superpose eq40502 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq40502
       grind)
    | exact resolve eq13 eq40502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40502
  have eq40538 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq40525
  have eq40539 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq40538
  have eq40546 : (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40539
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq40539
    | exact resolve eq40539 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40539
  have eq40552 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40546
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq40546
    | exact resolve eq40546 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40546
  have eq40555 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40552
       have i₂ := eq12950
       grind)
    | exact superpose eq12950 eq40552
    | exact resolve eq40552 eq12950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12950 eq40552
  have eq40853 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq40555
       grind)
    | exact superpose eq40555 eq10
    | exact resolve eq10 eq40555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40555
  have eq40994 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40853
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq40853
    | exact resolve eq40853 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40853
  have eq41342 : y ≠ y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1094 y x
       have i₂ := eq40994
       grind)
    | exact superpose eq40994 eq1094
    | (have j0 := eq1094 y x
       grind)
    | (have r₁ := eq1094 y x
       have r₂ := eq40994
       grind)
    | exact resolve eq1094 eq40994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094 eq40994
  have eq41380 : y ≠ y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq41342
  have eq41381 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq41380
  have eq41412 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40512
       have i₂ := eq41381
       grind)
    | exact superpose eq41381 eq40512
    | exact resolve eq40512 eq41381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40512 eq41381
  have eq41438 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq41412
  have eq41439 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq41438
  have eq41780 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq41439
       grind)
    | exact superpose eq41439 eq10
    | exact resolve eq10 eq41439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41439
  have eq41916 : x = y ∨ x = y := by
    first
    | (have i₁ := eq41780
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq41780
    | exact resolve eq41780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41780
  have eq41917 : x = y := by grind
  clear eq41916
  have eq41925 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41917
       grind)
    | exact superpose eq41917 eq16
    | exact resolve eq16 eq41917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41917
  have eq42030 : False := by grind
  exact eq42030

/-- `Equation1481`: `x = (y ◇ x) ◇ (x ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_Equation1481 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1481 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1481.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq276 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq278 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq289 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq276
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq276
    | exact resolve eq276 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq538 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq286
    | (have j0 := eq286 (σ X1) (σ X0)
       grind)
    | exact resolve eq286 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq286 (τ X0) X1
       grind)
    | exact superpose eq286 eq18
    | (have j1 := eq286 (τ X0) X1
       grind)
    | exact resolve eq18 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq286
  have eq3134 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq289
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq289
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq289 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3135 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq3134
  have eq6845 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq550 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq550
    | exact resolve eq550 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq6920 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6845 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq6845
    | (have j0 := eq6845 X0 X1
       grind)
    | exact resolve eq6845 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6845
  have eq61847 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq538 y x
       have i₂ := eq3135
       grind)
    | exact superpose eq3135 eq538
    | (have j0 := eq538 y x
       grind)
    | exact resolve eq538 eq3135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135
  have eq61852 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq61847
  have eq61857 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq61852
       have r₂ := eq289
       grind)
    | exact resolve eq61852 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61852
  have eq61858 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq61857
       have r₂ := eq16
       grind)
    | exact resolve eq61857 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61857
  have eq61860 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq289
       have i₂ := eq61858
       grind)
    | exact superpose eq61858 eq289
    | exact resolve eq289 eq61858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq61862 : x ≠ y ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq61858
       grind)
    | exact superpose eq61858 eq12
    | exact resolve eq12 eq61858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61863 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq61858
       grind)
    | exact superpose eq61858 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq61858
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq61858
       grind)
    | exact resolve eq13 eq61858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61858
  have eq61950 : x = y ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq61863
  have eq61951 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq61860
  have eq61974 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq61862
       have r₂ := eq61950
       grind)
    | exact resolve eq61862 eq61950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61862 eq61950
  have eq61986 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq538 y x
       have i₂ := eq61974
       grind)
    | exact superpose eq61974 eq538
    | (have j0 := eq538 y x
       grind)
    | exact resolve eq538 eq61974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq61974
  have eq62038 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq61986
  have eq62046 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq62038
       have r₂ := eq61951
       grind)
    | exact resolve eq62038 eq61951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61951 eq62038
  have eq62058 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq62046
       grind)
    | exact superpose eq62046 eq12
    | exact resolve eq12 eq62046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62059 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq62046
       grind)
    | exact superpose eq62046 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq62046
       grind)
    | exact resolve eq13 eq62046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62141 : (σ y) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq62046
  have eq62147 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq62059
  have eq62221 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq62147
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq62147
    | exact resolve eq62147 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62147
  have eq62222 : (σ y) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq62058
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq62058
    | exact resolve eq62058 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62058
  have eq62294 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq62221
       have r₂ := eq62141
       grind)
    | exact resolve eq62221 eq62141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62221
  have eq62295 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq62222
       have r₂ := eq62141
       grind)
    | exact resolve eq62222 eq62141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62141 eq62222
  have eq62360 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq62295
       have r₂ := eq62294
       grind)
    | exact resolve eq62295 eq62294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62294 eq62295
  have eq62403 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62360
       grind)
    | exact superpose eq62360 eq16
    | exact resolve eq16 eq62360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62360
  have eq62713 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq62403
       have i₂ := eq6920 x y
       grind)
    | exact superpose eq6920 eq62403
    | (have j1 := eq6920 x y
       grind)
    | (have r₁ := eq62403
       have r₂ := eq6920 x y
       grind)
    | exact resolve eq62403 eq6920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6920
  have eq62714 : x = (k y x) ∨ y = (M.op x y) := by grind
  clear eq62713
  have eq62727 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq62403
       have i₂ := eq62714
       grind)
    | exact superpose eq62714 eq62403
    | exact resolve eq62403 eq62714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62714
  have eq62741 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq62727
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq62727
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq62727 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62727
  have eq62742 : x = y ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq62741
  have eq62743 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq285 x y
       grind)
    | (have r₁ := eq62742
       have r₂ := eq285 x y
       grind)
    | (have r₁ := eq62742
       have r₂ := eq285 y x
       grind)
    | (have r₁ := eq62742
       have r₂ := eq285 y (M.op x y)
       grind)
    | exact resolve eq62742 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285 eq62742
  have eq62750 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq62403
       have i₂ := eq62743
       grind)
    | exact superpose eq62743 eq62403
    | exact resolve eq62403 eq62743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62743
  have eq62757 : y = (M.op x y) := by grind
  clear eq62750
  have eq62769 : x ≠ y ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq62757
       grind)
    | exact superpose eq62757 eq12
    | exact resolve eq12 eq62757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62770 : y ≠ y ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq62757
       grind)
    | exact superpose eq62757 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq62757
       grind)
    | exact resolve eq13 eq62757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62857 : x = y ∨ y = (k y x) := by grind
  clear eq62770
  have eq62880 : y = (k y x) := by
    first
    | (have r₁ := eq62769
       have r₂ := eq62857
       grind)
    | exact resolve eq62769 eq62857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62769 eq62857
  have eq62893 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq62403
       have i₂ := eq62880
       grind)
    | exact superpose eq62880 eq62403
    | exact resolve eq62403 eq62880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62403 eq62880
  have eq62957 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq62893
       have i₂ := eq62757
       grind)
    | exact superpose eq62757 eq62893
    | exact resolve eq62893 eq62757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62757 eq62893
  have eq62958 : False := by grind
  exact eq62958

/-- `Equation1481`: `x = (y ◇ x) ◇ (x ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation1481 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1481 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1481.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq70 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq106 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq106 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq122 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq107 (σ X0)
       grind)
    | exact superpose eq107 eq15
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq122 X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq122
    | exact resolve eq122 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq122
  have eq153 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq133
    | (have j1 := eq14 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact resolve eq133 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X1
       have j1 := eq153 X0 X1
       grind)
    | (have r₁ := eq190 X0 X1
       have r₂ := eq153 X0 X1
       grind)
    | (have r₁ := eq190 X0 (σ (M.op X0 X0))
       have r₂ := eq153 X0 X1
       grind)
    | (have r₁ := eq190 (M.op X0 X0) (σ X0)
       have r₂ := eq153 X0 X1
       grind)
    | exact resolve eq190 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq190
  have eq225 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq198 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq198
    | exact resolve eq198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq198 X0 (σ X1)
       grind)
    | exact superpose eq198 eq15
    | (have j1 := eq198 (k X1 X0) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq237 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq225 (τ X0) X1
       grind)
    | exact superpose eq225 eq19
    | (have j1 := eq225 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq225
  have eq325 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq237 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq237
    | exact resolve eq237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq350 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq325 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq325
    | (have j0 := eq325 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq325 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq1208 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq230 x y
       grind)
    | exact superpose eq230 eq16
    | (have j1 := eq230 x y
       grind)
    | exact resolve eq16 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq1227 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1208
       have i₂ := eq350 x y
       grind)
    | exact superpose eq350 eq1208
    | (have j1 := eq350 (σ x) (σ y)
       grind)
    | (have r₁ := eq1208
       have r₂ := eq350 x y
       grind)
    | (have r₁ := eq1208
       have r₂ := eq350 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1208
       have r₂ := eq350 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1208 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350 eq1208
  have eq1228 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1227
  have eq1230 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1228
       grind)
    | exact superpose eq1228 eq16
    | exact resolve eq16 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1231 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1230
       have r₂ := eq133 x
       grind)
    | exact resolve eq1230 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1232 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1231
       grind)
    | exact superpose eq1231 eq16
    | exact resolve eq16 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1233 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1231
       grind)
    | exact superpose eq1231 eq10
    | exact resolve eq10 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231
  have eq1279 : x = y := by
    first
    | (have i₁ := eq1233
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1233
    | exact resolve eq1233 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq1280 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1232
       have i₂ := eq133 x
       grind)
    | exact superpose eq133 eq1232
    | exact resolve eq1232 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq1232
  have eq1282 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1280
       have i₂ := eq1279
       grind)
    | exact superpose eq1279 eq1280
    | exact resolve eq1280 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279 eq1280
  have eq1283 : False := by grind
  exact eq1283

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_pyx_x_pyx_Equation1483 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq78 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k y x) := by
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
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq96 y x
       grind)
    | exact superpose eq96 eq75
    | (have j1 := eq96 y x
       grind)
    | exact resolve eq75 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
    | (have j0 := eq96 (σ y) (σ x)
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
  have eq716 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq717 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
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
  have eq737 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq729 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq729
       grind)
    | exact resolve eq13 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq745 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq737
  have eq751 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq838 : y ≠ y ∨ y = (M.op y x) ∨ y = (k y x) := by
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
  have eq844 : y = (k y x) ∨ y = (M.op y x) := by grind
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
  have eq2040 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq844
       grind)
    | exact superpose eq844 eq75
    | exact resolve eq75 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq2047 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq850 eq2040
    | exact resolve eq2040 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq2049 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
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
  have eq2050 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
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
    | (have j0 := eq96 (σ (M.op x y)) (σ x)
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
  have eq2069 : y ≠ y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2059
       grind)
    | exact superpose eq2059 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2059
       grind)
    | exact resolve eq13 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq2081 : (M.op x y) = (k y x) := by grind
  clear eq2069
  have eq2084 : (M.op x y) = (k y x) := by
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
  have eq2091 : y = (k y x) := by
    first
    | exact superpose eq830 eq2084
    | exact resolve eq2084 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq2084
  have eq2186 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq2091
       grind)
    | exact superpose eq2091 eq75
    | exact resolve eq75 eq2091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq2091
  have eq2193 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq850 eq2186
    | exact resolve eq2186 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2186
  have eq2195 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq2196 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
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
    | (have j0 := eq96 (σ (M.op x y)) (σ x)
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
