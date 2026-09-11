import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1590`: `x = (y ◇ z) ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxy_pyx_Equation1590 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1590 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1590.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X1 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X0)) = (M.op (M.op (M.op X1 X2) X3) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X1 X0)) (M.op X1 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) X1 (M.op X2 X1)
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq79 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq81 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq79 (σ X0)
       grind)
    | exact superpose eq79 eq10
    | exact resolve eq10 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq44
    | exact resolve eq44 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq83 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq79 sF2
       grind)
    | exact superpose eq79 eq50
    | exact resolve eq50 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq84 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq83
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq83
    | exact resolve eq83 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq85 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq79 sF2
       grind)
    | exact superpose eq79 eq82
    | exact resolve eq82 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq86 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq81
    | exact resolve eq81 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq93 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq79 sF3
       grind)
    | exact superpose eq79 eq77
    | exact resolve eq77 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq94 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq93
       have i₂ := eq79 y
       grind)
    | exact superpose eq79 eq93
    | exact resolve eq93 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq106
    | exact resolve eq106 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq107
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107
    | exact resolve eq107 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq135 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq138 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq135
       have i₂ := eq79 sF1
       grind)
    | exact superpose eq79 eq135
    | exact resolve eq135 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq140 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq138
       have i₂ := eq79 sF0
       grind)
    | exact superpose eq79 eq138
    | exact resolve eq138 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq138
  have eq161 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq140 eq16
    | exact resolve eq16 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq234 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq238 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 : G, (M.op x (M.op (M.op x y) (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq234 (M.op sF0 (M.op y X0))
       have i₂ := eq14 X0 y sF0
       grind)
    | exact superpose eq14 eq234
    | exact resolve eq234 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq14
    | exact resolve eq14 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq559 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq420 eq14
    | exact resolve eq14 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq570 : ∀ X0 : G, (M.op y (M.op x (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq559 (M.op x (M.op sF0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq559
    | exact resolve eq559 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq631 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X3 (M.op X0 X3))) (M.op X0 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X3 (M.op X0 X3))
       have i₂ := eq57 (M.op X1 X2) X3 X0
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1674 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1675 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1674
    | exact resolve eq1674 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq1678 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1675
       have r₂ := eq28
       grind)
    | exact resolve eq1675 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1675
  have eq1680 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1678
    | exact resolve eq1678 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678
  have eq1685 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1680 eq68
    | (have r₁ := eq68
       have r₂ := eq1680
       grind)
    | exact resolve eq68 eq1680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1686 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1680 eq238
    | exact resolve eq238 eq1680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq1693 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1685
  have eq1879 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1693 eq108
    | exact resolve eq108 eq1693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1693
  have eq1883 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1879
  have eq1891 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1883 eq1686
    | exact resolve eq1686 eq1883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686
  have eq1908 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1891
  have eq2004 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1908 eq52
    | exact resolve eq52 eq1908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1908
  have eq2230 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1680 eq2004
    | exact resolve eq2004 eq1680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680 eq2004
  have eq2251 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2230
  have eq2303 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2251 eq14
    | exact resolve eq14 eq2251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2585 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1883 eq2303
    | exact resolve eq2303 eq1883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883 eq2303
  have eq2603 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2585
  have eq2695 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2603 eq161
    | exact resolve eq161 eq2603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq2603
  have eq2711 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq2695
    | exact resolve eq2695 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2695
  have eq2715 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2711 eq570
    | exact resolve eq570 eq2711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq2718 : y = (M.op (M.op x (M.op x y)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2711 eq54
    | exact resolve eq54 eq2711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2735 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2715
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2715
    | exact resolve eq2715 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2715
  have eq2738 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2735 eq234
    | exact resolve eq234 eq2735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq2735
  have eq4412 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2738 eq2711
    | exact resolve eq2711 eq2738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711 eq2738
  have eq4463 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4412
  have eq4482 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4463 eq2718
    | exact resolve eq2718 eq4463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2718 eq4463
  have eq4511 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4482
  have eq4686 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq4511
       grind)
    | exact superpose eq4511 eq94
    | exact resolve eq94 eq4511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq4511
  have eq4708 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4686
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4686
    | exact resolve eq4686 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4686
  have eq4710 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4708 eq2251
    | exact resolve eq2251 eq4708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251 eq4708
  have eq4733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4710
  have eq4738 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq4733
    | exact resolve eq4733 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4733
  have eq4739 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq4738
       have r₂ := eq28
       grind)
    | exact resolve eq4738 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4738
  have eq4933 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4739 eq30
    | exact resolve eq30 eq4739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4739
  have eq4966 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq4933
    | exact resolve eq4933 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4933
  have eq4967 : x = (M.op x y) ∨ x = y := by grind
  clear eq4966
  have eq4970 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq4967 eq21
    | exact resolve eq21 eq4967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4973 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4967 eq54
    | exact resolve eq54 eq4967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq4967
  have eq5005 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq4970
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4970
    | exact resolve eq4970 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4970
  have eq10527 : ∀ X0 : G, (σ (M.op x x)) = (M.op (M.op (σ (M.op x x)) X0) (M.op X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq548 (M.op x x) X0
       have i₂ := eq4973 x
       grind)
    | exact superpose eq4973 eq548
    | exact resolve eq548 eq4973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq4973
  have eq10568 : ∀ X0 : G, (σ (M.op x x)) = (M.op (M.op (σ (M.op x x)) X0) (M.op X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10527 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10527
    | (have j0 := eq10527 X0
       grind)
    | exact resolve eq10527 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10527
  have eq10593 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ x)) X0) (M.op X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10568 X0
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq10568
    | exact resolve eq10568 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq10568
  have eq10599 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq10593 x
       have i₂ := eq56 sF3 sF2 sF2 x
       grind)
    | exact superpose eq56 eq10593
    | exact resolve eq10593 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq10593
  have eq10600 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq27 eq10599
    | exact resolve eq10599 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10599
  have eq11795 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op X0 (M.op X1 X0))) (M.op X1 (M.op (σ x) (σ x)))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq10600 eq631
    | exact resolve eq631 eq10600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10600
  have eq11820 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq11795 x x
       have i₂ := eq631 x sF2 sF2 x
       grind)
    | exact superpose eq631 eq11795
    | exact resolve eq11795 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq11795
  have eq11832 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq11820 eq28
    | exact resolve eq28 eq11820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11820
  have eq11876 : x = y := by
    first
    | (have r₁ := eq11832
       have r₂ := eq5005
       grind)
    | exact resolve eq11832 eq5005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5005 eq11832
  have eq11877 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq11876
       grind)
    | exact superpose eq11876 eq19
    | exact resolve eq19 eq11876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq11878 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq11876
       grind)
    | exact superpose eq11876 eq25
    | exact resolve eq25 eq11876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11876
  have eq11921 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11878
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11878
    | exact resolve eq11878 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11878
  have eq11924 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11921 eq27
    | exact resolve eq27 eq11921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq11921
  have eq12622 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11924 eq84
    | exact resolve eq84 eq11924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq11924
  have eq12691 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq12622
       have i₂ := eq11877
       grind)
    | exact superpose eq11877 eq12622
    | exact resolve eq12622 eq11877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11877 eq12622
  have eq12697 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12691 eq15
    | exact resolve eq15 eq12691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12691
  have eq12739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq12697
    | exact resolve eq12697 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq12697
  have eq12748 : False := by grind
  exact eq12748

/-- `Equation1590`: `x = (y ◇ z) ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pyy_pxy_Equation1590 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1590 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1590.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq18
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X0)) (M.op (M.op X1 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X2) (M.op X2 (M.op X1 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X0)) = (M.op (M.op (M.op X1 X2) X3) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X1 X0)) (M.op X1 X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X2 X1)
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op (M.op X2 (M.op X1 X0)) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X3 (M.op X2 (M.op X1 X0)) (M.op X1 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X0 X1)
       have i₂ := eq64 (M.op (M.op X0 X1) (M.op X1 X2)) X1 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X1) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X1 (M.op X0 X1) X2
       have i₂ := eq64 (M.op (M.op X0 X1) X2) X1 X0
       grind)
    | exact superpose eq64 eq71
    | exact resolve eq71 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op X1 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X2 (M.op X1 X0) (M.op (M.op X1 X0) X1)
       have i₂ := eq71 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq71 eq64
    | exact resolve eq64 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op (M.op X0 (M.op X2 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq89 (M.op X1 (M.op X2 X0)) (M.op X2 X1) X3
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq89
    | exact resolve eq89 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq89 (M.op (M.op X1 X2) (M.op X2 X0)) X1 X3
       have i₂ := eq71 X1 X2 X0
       grind)
    | exact superpose eq71 eq89
    | exact resolve eq89 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 (M.op X3 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X1 X3 X2 (M.op X2 (M.op X3 X0))
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq257 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X1 X0) X4)) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X3 X2) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 X4 (M.op X1 X0) X3 (M.op X3 X2)
       have i₂ := eq63 X2 X1 X0 X3
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) = (M.op (M.op (M.op X2 X1) (M.op X4 X3)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 (M.op X3 (M.op X4 X0)) X2 X1 (M.op X4 X3)
       have i₂ := eq9 X0 X4 X3
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op (M.op X3 X4) X0)))) = (M.op (M.op (M.op X2 X1) X4) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 (M.op X3 (M.op (M.op X3 X4) X0)) X2 X1 X4
       have i₂ := eq86 X3 X4 X0
       grind)
    | exact superpose eq86 eq63
    | exact resolve eq63 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq124 X0 X1 X2 X3
       have i₂ := eq260 X3 X2 X1 X0 X2
       grind)
    | exact superpose eq260 eq124
    | exact resolve eq124 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq451 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5) = (M.op (M.op (M.op X4 (M.op X0 (M.op X1 X2))) (M.op X3 X2)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq67 (M.op X3 X2) (M.op (M.op X1 X0) X3) X4 X5
       have i₂ := eq63 X2 X1 X0 X3
       grind)
    | exact superpose eq63 eq67
    | exact resolve eq67 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5) = (M.op (M.op X2 (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2))))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq451 X0 X1 X2 X3 X4 X5
       have i₂ := eq121 X2 (M.op X4 (M.op X0 (M.op X1 X2))) X3 X5
       grind)
    | (have i₁ := eq451 X0 X1 X2 X3 X4 X5
       have i₂ := eq121 (M.op X4 (M.op X0 (M.op X1 X2))) X2 X3 X5
       grind)
    | exact superpose eq121 eq451
    | exact resolve eq451 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq547 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X1 X0) X4) X5)) = (M.op (M.op X4 X2) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq181 X5 (M.op X4 X2) X3 (M.op (M.op X1 X0) X4)
       have i₂ := eq63 X2 X1 X0 X4
       grind)
    | exact superpose eq63 eq181
    | exact resolve eq181 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq181 X1 X3 (M.op (M.op X2 X3) X0) X2
       have i₂ := eq89 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq89 eq181
    | exact resolve eq181 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X3)) X2) = (M.op (M.op X3 X4) (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X0 (M.op X1 X3)) X2) X3 X4
       have i₂ := eq181 X2 X3 X0 X1
       grind)
    | exact superpose eq181 eq9
    | exact resolve eq9 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X4)) X2) = (M.op X3 (M.op (M.op X3 X4) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq71 X3 X4 (M.op (M.op X0 (M.op X1 X4)) X2)
       have i₂ := eq181 X2 X4 X0 X1
       grind)
    | exact superpose eq181 eq71
    | exact resolve eq71 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) = (M.op (M.op X0 (M.op X1 (M.op X4 X3))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq86 X4 X3 (M.op (M.op X0 (M.op X1 (M.op X4 X3))) X2)
       have i₂ := eq181 X2 (M.op X4 X3) X0 X1
       grind)
    | exact superpose eq181 eq86
    | exact resolve eq86 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq181
  have eq595 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5) = (M.op (M.op X0 (M.op X1 X2)) (M.op X4 (M.op X2 (M.op X3 X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq522 X0 X1 X2 X3 X4 X5
       have i₂ := eq589 X2 X3 X5 (M.op X0 (M.op X1 X2)) X4
       grind)
    | exact superpose eq589 eq522
    | exact resolve eq522 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq628 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X1 X0) X4) X5)) = (M.op (M.op X4 X2) (M.op X2 (M.op X1 (M.op X3 (M.op X0 X5))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq547 X0 X1 X2 X3 X4 X5
       have i₂ := eq589 X3 X0 X5 X2 X1
       grind)
    | exact superpose eq589 eq547
    | exact resolve eq547 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq644 : ∀ X0 X1 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X1 X0) X4) X5)) = (M.op (M.op X1 (M.op X3 X4)) (M.op X0 X5)) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq628 X0 X1 x X3 X4 X5
       have i₂ := eq578 X1 X3 (M.op X0 X5) X4 x
       grind)
    | exact superpose eq578 eq628
    | exact resolve eq628 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq628
  have eq655 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X1 X0) X4)) = (M.op X1 (M.op (M.op (M.op X0 (M.op X3 X2)) X2) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq257 X0 X1 X2 X3 X4
       have i₂ := eq644 (M.op X3 X2) X0 X1 X2 X4
       grind)
    | exact superpose eq644 eq257
    | exact resolve eq257 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq656 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5) = (M.op X1 (M.op (M.op (M.op X0 X4) X2) (M.op X2 (M.op X3 X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq595 X0 X1 X2 X3 X4 X5
       have i₂ := eq644 X4 X0 X1 X2 (M.op X2 (M.op X3 X5))
       grind)
    | exact superpose eq644 eq595
    | exact resolve eq595 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq644
  have eq660 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5) = (M.op X1 (M.op X4 (M.op X0 (M.op X3 X5)))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq656 X0 X1 x X3 X4 X5
       have i₂ := eq63 (M.op X3 X5) X0 X4 x
       grind)
    | exact superpose eq63 eq656
    | exact resolve eq656 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq656
  have eq661 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op (M.op X1 X0) X4)) = (M.op X1 (M.op (M.op X3 X0) X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq655 X0 X1 x X3 X4
       have i₂ := eq67 x X3 X0 X4
       grind)
    | exact superpose eq67 eq655
    | exact resolve eq655 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq757 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) X1) X4) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq67 X3 (M.op X0 X2) X1 X4
       have i₂ := eq661 X2 X0 X1 X3
       grind)
    | (have i₁ := eq67 X3 (M.op X0 X2) X1 X4
       have i₂ := eq661 X2 X1 X0 X3
       grind)
    | exact superpose eq661 eq67
    | exact resolve eq67 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq810 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X0 X2) X1) X4) = (M.op (M.op (M.op X1 X2) X0) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq757 X0 X1 X2 x X4
       have i₂ := eq67 x (M.op X1 X2) X0 X4
       grind)
    | exact superpose eq67 eq757
    | exact resolve eq757 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq757
  have eq2797 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2853 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 (M.op X0 X1)) X2) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X2 X1 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq64 X0 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq64
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2925 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2797 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2797
  have eq2926 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2925 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2925
  have eq2943 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 X2) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2853 X0 X1 X2
       have i₂ := eq64 X2 X1 X0
       grind)
    | exact superpose eq64 eq2853
    | (have j0 := eq2853 X0 X1 X2
       grind)
    | exact resolve eq2853 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2853
  have eq3119 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X4 X3) (M.op (M.op X2 X1) X0)) X5) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq810 X4 (M.op (M.op X2 X1) X0) X3 X5
       have i₂ := eq810 X2 X0 X1 X3
       grind)
    | (have i₁ := eq810 X4 (M.op (M.op X2 X1) X0) X3 X5
       have i₂ := eq810 X0 X2 X1 X3
       grind)
    | exact superpose eq810 eq810
    | exact resolve eq810 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3446 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X4 X3) (M.op (M.op X2 X1) X0)) X5) = (M.op (M.op X0 X1) (M.op X4 (M.op X2 (M.op X3 X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3119 X0 X1 X2 X3 X4 X5
       have i₂ := eq660 X2 (M.op X0 X1) X3 X4 X5
       grind)
    | exact superpose eq660 eq3119
    | exact resolve eq3119 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq3119
  have eq3600 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X4 (M.op X2 (M.op X3 X5)))) = (M.op X3 (M.op X4 (M.op X0 (M.op (M.op X2 X1) X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3446 X0 X1 X2 X3 X4 X5
       have i₂ := eq260 X5 X3 X4 X0 (M.op X2 X1)
       grind)
    | exact superpose eq260 eq3446
    | exact resolve eq3446 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3446
  have eq7622 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2926 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2926
  have eq7625 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq7622 X0 X1
       have j1 := eq2943 X1 X0 x
       grind)
    | (have r₁ := eq7622 X0 x
       have r₂ := eq2943 X0 x x
       grind)
    | (have r₁ := eq7622 X1 x
       have r₂ := eq2943 x X1 x
       grind)
    | (have r₁ := eq7622 X0 X0
       have r₂ := eq2943 X0 (M.op X0 X0) x
       grind)
    | exact resolve eq7622 eq2943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2943 eq7622
  have eq7823 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq7968 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq7823 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7823
  have eq8033 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7968 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7968
  have eq8184 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq8033 (σ X0)
       grind)
    | exact superpose eq8033 eq15
    | exact resolve eq15 eq8033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8186 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq8033 (τ X0)
       grind)
    | exact superpose eq8033 eq32
    | exact resolve eq32 eq8033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8201 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8186 X0
       have i₂ := eq8033 X0
       grind)
    | exact superpose eq8033 eq8186
    | exact resolve eq8186 eq8033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8186
  have eq8203 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8184 X0
       have i₂ := eq8033 X0
       grind)
    | exact superpose eq8033 eq8184
    | exact resolve eq8184 eq8033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8033 eq8184
  have eq8542 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1
       have i₂ := eq8201 X0
       grind)
    | exact superpose eq8201 eq9
    | exact resolve eq9 eq8201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8546 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (M.op (τ X0) (τ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (τ X0) (τ X0)
       have i₂ := eq8201 X0
       grind)
    | exact superpose eq8201 eq64
    | exact resolve eq64 eq8201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8548 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X1 (τ X0) (τ X0)
       have i₂ := eq8201 X0
       grind)
    | exact superpose eq8201 eq71
    | exact resolve eq71 eq8201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8549 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (τ X0) (τ X0) X1
       have i₂ := eq8201 X0
       grind)
    | exact superpose eq8201 eq71
    | exact resolve eq71 eq8201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8555 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (M.op (τ (M.op X0 X0)) (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (τ X0) (τ X0) X1
       have i₂ := eq8201 X0
       grind)
    | exact superpose eq8201 eq89
    | exact resolve eq89 eq8201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq8587 : ∀ X0 : G, (k (τ (M.op X0 X0)) (τ X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  have eq8591 : ∀ X0 : G, (τ (k (M.op X0 X0) X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8587 X0
       have i₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact superpose eq32 eq8587
    | exact resolve eq8587 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq8587
  have eq8604 : ∀ X0 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq8591
  have eq8615 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ (M.op X0 (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8546 X0 X1
       have i₂ := eq8604 X0
       grind)
    | exact superpose eq8604 eq8546
    | exact resolve eq8546 eq8604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8546
  have eq8636 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (σ X0) (σ X0)
       have i₂ := eq8203 X0
       grind)
    | exact superpose eq8203 eq64
    | exact resolve eq64 eq8203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq8638 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X1 (σ X0) (σ X0)
       have i₂ := eq8203 X0
       grind)
    | exact superpose eq8203 eq71
    | exact resolve eq71 eq8203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq8672 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7625 X1 (σ X0)
       have i₂ := eq8203 X0
       grind)
    | exact superpose eq8203 eq7625
    | (have j0 := eq7625 X1 (σ X0)
       grind)
    | exact resolve eq7625 eq8203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8677 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq8681 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8677 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq8677
    | exact resolve eq8677 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8677
  have eq8686 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq8681
  have eq8704 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8636 X0 X1
       have i₂ := eq8686 X0
       grind)
    | exact superpose eq8686 eq8636
    | exact resolve eq8636 eq8686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8636 eq8686
  have eq9711 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ X0) (τ (M.op X0 X0))) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq8542 X0 (τ (M.op X0 X0))
       have i₂ := eq8201 (M.op X0 X0)
       grind)
    | exact superpose eq8201 eq8542
    | exact resolve eq8542 eq8201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8201
  have eq9793 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (τ X0) X2) X3) = (M.op (M.op (M.op X2 (M.op X1 (τ (M.op X0 X0)))) (M.op (τ X0) X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq810 (M.op (τ X0) X1) X2 (M.op X1 (τ (M.op X0 X0))) X3
       have i₂ := eq8542 X0 X1
       grind)
    | exact superpose eq8542 eq810
    | exact resolve eq810 eq8542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8542
  have eq9794 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (τ X0) X2) X3) = (M.op (M.op X1 (M.op (τ X0) (M.op X2 (M.op X1 (τ (M.op X0 X0)))))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9793 X0 X1 X2 X3
       have i₂ := eq121 X1 (M.op X2 (M.op X1 (τ (M.op X0 X0)))) (τ X0) X3
       grind)
    | (have i₁ := eq9793 X0 X1 X2 X3
       have i₂ := eq121 (M.op X2 (M.op X1 (τ (M.op X0 X0)))) X1 (τ X0) X3
       grind)
    | exact superpose eq121 eq9793
    | exact resolve eq9793 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq9793
  have eq9849 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 (M.op X0 X0))) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9711 X0
       have i₂ := eq8604 X0
       grind)
    | exact superpose eq8604 eq9711
    | exact resolve eq9711 eq8604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8604 eq9711
  have eq9897 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (τ X0) X2) X3) = (M.op (M.op X1 (τ (M.op X0 X0))) (M.op X2 (M.op X1 (M.op (τ X0) X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9794 X0 X1 X2 X3
       have i₂ := eq589 X1 (τ X0) X3 (M.op X1 (τ (M.op X0 X0))) X2
       grind)
    | exact superpose eq589 eq9794
    | exact resolve eq9794 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq9794
  have eq9910 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9849 X0
       have i₂ := eq8615 X0 (τ (M.op (M.op X0 X0) (M.op X0 X0)))
       grind)
    | exact superpose eq8615 eq9849
    | exact resolve eq9849 eq8615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8615 eq9849
  have eq9943 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (τ X0) X2) X3) = (M.op (τ X0) (M.op X2 (M.op X1 (M.op (M.op X1 (τ (M.op X0 X0))) X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9897 X0 X1 X2 X3
       have i₂ := eq3600 X1 (τ (M.op X0 X0)) X1 (τ X0) X2 X3
       grind)
    | exact superpose eq3600 eq9897
    | exact resolve eq9897 eq3600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3600 eq9897
  have eq9961 : ∀ X0 X2 X3 : G, (M.op (M.op (τ X0) X2) X3) = (M.op (M.op (M.op X2 (τ X0)) (τ (M.op X0 X0))) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9943 X0 x X2 X3
       have i₂ := eq265 X3 (τ X0) X2 x (τ (M.op X0 X0))
       grind)
    | exact superpose eq265 eq9943
    | exact resolve eq9943 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq9943
  have eq10330 : ∀ X0 X1 : G, (M.op (M.op (τ X1) (τ X0)) (τ (M.op X0 X0))) = (M.op (τ X1) (M.op (τ (M.op X1 X1)) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8549 X1 (M.op (M.op (τ X1) (τ X0)) (τ (M.op X0 X0)))
       have i₂ := eq8548 X0 (τ X1)
       grind)
    | exact superpose eq8548 eq8549
    | exact resolve eq8549 eq8548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8549
  have eq10844 : ∀ X0 X1 : G, (M.op (σ (M.op (τ (M.op X0 X0)) (τ X0))) X1) = (M.op (σ (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ X0))))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8704 (M.op (τ (M.op X0 X0)) (τ X0)) X1
       have i₂ := eq8555 X0 (M.op (τ (M.op X0 X0)) (τ X0))
       grind)
    | exact superpose eq8555 eq8704
    | exact resolve eq8704 eq8555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8704
  have eq10982 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (M.op (σ (M.op (τ (M.op X0 X0)) (τ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10844 X0 X1
       have i₂ := eq9 (τ X0) (τ (M.op X0 X0)) (τ X0)
       grind)
    | exact superpose eq9 eq10844
    | exact resolve eq10844 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10844
  have eq11047 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ (M.op (τ (M.op X0 X0)) (τ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10982 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10982
    | exact resolve eq10982 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10982
  have eq12284 : ∀ X0 X1 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op X1 (M.op (M.op X1 (σ (M.op (τ (M.op X0 X0)) (τ X0)))) (σ (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq8638 (M.op (τ (M.op X0 X0)) (τ X0)) X1
       have i₂ := eq8555 X0 (M.op (τ (M.op X0 X0)) (τ X0))
       grind)
    | exact superpose eq8555 eq8638
    | exact resolve eq8638 eq8555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8555 eq8638
  have eq14039 : ∀ X0 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (τ X0) (M.op (τ X0) (τ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0)))))) := by
    intro X0
    first
    | (have i₁ := eq8548 (M.op (M.op X0 X0) (M.op X0 X0)) (τ X0)
       have i₂ := eq9910 X0
       grind)
    | exact superpose eq9910 eq8548
    | exact resolve eq8548 eq9910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8548
  have eq14070 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (τ (M.op (M.op X0 X0) (M.op X0 X0))))) = (M.op (M.op (M.op (τ X0) X1) X2) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq561 X2 (τ (M.op (M.op X0 X0) (M.op X0 X0))) (τ X0) X1
       have i₂ := eq9910 X0
       grind)
    | exact superpose eq9910 eq561
    | exact resolve eq561 eq9910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq9910
  have eq14085 : ∀ X0 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (τ X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq14039 X0
       have i₂ := eq14070 (M.op X0 X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq14070 eq14039
    | exact resolve eq14039 eq14070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14039 eq14070
  have eq14150 : ∀ X0 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op (τ X0) (τ X0)) (τ (M.op X0 X0))) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq14085 X0
       have i₂ := eq810 (τ (M.op X0 X0)) (τ X0) (τ X0) (τ (M.op X0 X0))
       grind)
    | (have i₁ := eq14085 X0
       have i₂ := eq810 (τ X0) (τ (M.op X0 X0)) (τ X0) (τ (M.op X0 X0))
       grind)
    | exact superpose eq810 eq14085
    | exact resolve eq14085 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq14085
  have eq14189 : ∀ X0 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (τ X0) (τ X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq14150 X0
       have i₂ := eq9961 X0 (τ X0) (τ (M.op X0 X0))
       grind)
    | exact superpose eq9961 eq14150
    | exact resolve eq14150 eq9961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9961 eq14150
  have eq14218 : ∀ X0 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq14189 X0
       have i₂ := eq10330 X0 X0
       grind)
    | exact superpose eq10330 eq14189
    | exact resolve eq14189 eq10330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10330 eq14189
  have eq14251 : ∀ X0 X1 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op X1 (M.op (M.op X1 (σ (M.op (τ (M.op X0 X0)) (τ X0)))) (σ (τ (M.op (M.op X0 X0) (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq12284 X0 X1
       have i₂ := eq14218 X0
       grind)
    | exact superpose eq14218 eq12284
    | exact resolve eq12284 eq14218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12284 eq14218
  have eq14278 : ∀ X0 X1 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op X1 (M.op (M.op X1 (σ (M.op (τ (M.op X0 X0)) (τ X0)))) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14251 X0 X1
       have i₂ := eq11 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq11 eq14251
    | exact resolve eq14251 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14251
  have eq14298 : ∀ X0 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 (σ (M.op (τ (M.op X0 X0)) (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq14278 X0 x
       have i₂ := eq583 (M.op X0 X0) X0 X0 x (σ (M.op (τ (M.op X0 X0)) (τ X0)))
       grind)
    | exact superpose eq583 eq14278
    | exact resolve eq14278 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq14278
  have eq14313 : ∀ X0 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op X0 (M.op X0 (M.op (σ (M.op (τ (M.op X0 X0)) (τ X0))) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq14298 X0
       have i₂ := eq260 X0 X0 X0 (σ (M.op (τ (M.op X0 X0)) (τ X0))) X0
       grind)
    | exact superpose eq260 eq14298
    | exact resolve eq14298 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq14298
  have eq14323 : ∀ X0 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op (M.op (σ (M.op (τ (M.op X0 X0)) (τ X0))) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14313 X0
       have i₂ := eq291 (σ (M.op (τ (M.op X0 X0)) (τ X0))) X0 X0 X0
       grind)
    | exact superpose eq291 eq14313
    | exact resolve eq14313 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq14313
  have eq14331 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq14323 X0
       have i₂ := eq11047 X0 X0
       grind)
    | exact superpose eq11047 eq14323
    | exact resolve eq14323 eq11047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11047 eq14323
  have eq15055 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq14331 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14331
    | exact resolve eq14331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14331
  have eq15100 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ (M.op X0 X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq15055 X0
       have i₂ := eq8203 X0
       grind)
    | exact superpose eq8203 eq15055
    | exact resolve eq15055 eq8203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8203 eq15055
  have eq15137 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15100 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq15100
    | exact resolve eq15100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15100
  have eq20804 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq8672 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq8672 X0 (σ X0)
       grind)
    | exact superpose eq8672 eq10
    | (have j1 := eq8672 X1 X0
       grind)
    | exact resolve eq10 eq8672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8672
  have eq23759 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq20804 (σ X0) X1
       grind)
    | exact superpose eq20804 eq15
    | (have j1 := eq20804 (σ X0) X1
       grind)
    | exact resolve eq15 eq20804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20804
  have eq23774 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23759 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23759
    | (have j0 := eq23759 X0 X1
       grind)
    | exact resolve eq23759 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23759
  have eq26164 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23774 X0 X1
       have i₂ := eq7625 X0 X1
       grind)
    | exact superpose eq7625 eq23774
    | (have j0 := eq23774 X0 X1
       have j1 := eq7625 X0 X1
       grind)
    | exact resolve eq23774 eq7625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7625 eq23774
  have eq26373 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq26164 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26164
  have eq27609 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15137 X1
       have i₂ := eq26373 X0 X1
       grind)
    | (have i₁ := eq15137 X0
       have i₂ := eq26373 (M.op X0 X0) X1
       grind)
    | exact superpose eq26373 eq15137
    | (have j1 := eq26373 X0 X1
       grind)
    | exact resolve eq15137 eq26373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15137 eq26373
  have eq27747 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq27609 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27609
  have eq28217 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27747 x y
       grind)
    | exact superpose eq27747 eq16
    | (have r₁ := eq16
       have r₂ := eq27747 x y
       grind)
    | exact resolve eq16 eq27747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27747
  have eq28219 : False := by grind
  exact eq28219

/-- `Equation1630`: `x = (x ◇ x) ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pxx_pxy_Equation1630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq263 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq263 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq263 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq263 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq275 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq264 (σ X0)
       grind)
    | exact superpose eq264 eq15
    | exact resolve eq15 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq264 (τ X0)
       grind)
    | exact superpose eq264 eq31
    | exact resolve eq31 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq288 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq281
    | exact resolve eq281 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq294 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq275
    | exact resolve eq275 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq275
  have eq338 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq9
    | exact resolve eq9 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (σ X0)
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq450 X0 X1
       have j1 := eq338 X0 X1
       grind)
    | (have r₁ := eq450 X0 X1
       have r₂ := eq338 X0 X1
       grind)
    | exact resolve eq450 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338 eq450
  have eq526 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq487 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq487
    | (have j0 := eq487 (τ X0) X1
       grind)
    | exact resolve eq487 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq487 X1 (σ X0)
       grind)
    | exact superpose eq487 eq15
    | (have j1 := eq487 X1 (σ X0)
       grind)
    | exact resolve eq15 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq556 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq537 X0 X1
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq537
    | (have j0 := eq537 X0 X1
       grind)
    | exact resolve eq537 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq560 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (M.op X0 X0))) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq526 X0 X1
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq526
    | (have j0 := eq526 X0 X1
       grind)
    | exact resolve eq526 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq566 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq560
    | (have j0 := eq560 X0 X1
       grind)
    | exact resolve eq560 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq589 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq566 X1 (τ X0)
       grind)
    | exact superpose eq566 eq17
    | (have j1 := eq566 X1 (τ X0)
       grind)
    | exact resolve eq17 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq566
  have eq598 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq589 X0 X1
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq589
    | (have j0 := eq589 X0 X1
       grind)
    | exact resolve eq589 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq589
  have eq783 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq598 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq598
    | (have j0 := eq598 (σ X0) X1
       grind)
    | exact resolve eq598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq842 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq783 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq783
    | (have j0 := eq783 X0 X1
       grind)
    | exact resolve eq783 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq850 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq842 X0 X1
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq842
    | (have j0 := eq842 X0 X1
       grind)
    | exact resolve eq842 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq854 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq850 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq850
    | (have j0 := eq850 X0 X1
       grind)
    | exact resolve eq850 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq1178 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq556 x y
       grind)
    | exact superpose eq556 eq16
    | (have j1 := eq556 x y
       grind)
    | exact resolve eq16 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq1215 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1178
       have i₂ := eq854 x y
       grind)
    | exact superpose eq854 eq1178
    | (have j1 := eq854 x y
       grind)
    | (have r₁ := eq1178
       have r₂ := eq854 x y
       grind)
    | exact resolve eq1178 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq1178
  have eq1216 : (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq1215
  have eq1219 : ∀ X0 : G, y = (M.op (M.op x x) (M.op (M.op x x) X0)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq9 y x
       have i₂ := eq1216
       grind)
    | exact superpose eq1216 eq9
    | exact resolve eq9 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1246 : x = y ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1219 x
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq1219
    | exact resolve eq1219 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1247 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1246
       grind)
    | exact superpose eq1246 eq16
    | exact resolve eq16 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1248 : (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1247
       have r₂ := eq294 x
       grind)
    | exact resolve eq1247 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq1252 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (M.op (σ (M.op x x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq340 y x
       have i₂ := eq1248
       grind)
    | exact superpose eq1248 eq340
    | exact resolve eq340 eq1248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq1303 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1252 x
       have i₂ := eq340 x x
       grind)
    | exact superpose eq340 eq1252
    | exact resolve eq1252 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340 eq1252
  have eq1304 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1303
       grind)
    | exact superpose eq1303 eq16
    | exact resolve eq16 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1305 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1303
       grind)
    | exact superpose eq1303 eq10
    | exact resolve eq10 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303
  have eq1358 : x = y := by
    first
    | (have i₁ := eq1305
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1305
    | exact resolve eq1305 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1359 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1304
       have i₂ := eq294 x
       grind)
    | exact superpose eq294 eq1304
    | exact resolve eq1304 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq1304
  have eq1360 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1359
       have i₂ := eq1358
       grind)
    | exact superpose eq1358 eq1359
    | exact resolve eq1359 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358 eq1359
  have eq1361 : False := by grind
  exact eq1361

/-- `Equation1630`: `x = (x ◇ x) ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation1630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1630.models_iff G M).mp hM
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
  have eq64 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq87 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq88 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq87 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq103 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq88 (σ X0)
       grind)
    | exact superpose eq88 eq15
    | exact resolve eq15 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq88 (τ X0)
       grind)
    | exact superpose eq88 eq32
    | exact resolve eq32 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq112 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105 X0
       have i₂ := eq88 X0
       grind)
    | exact superpose eq88 eq105
    | exact resolve eq105 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq103 X0
       have i₂ := eq88 X0
       grind)
    | exact superpose eq88 eq103
    | exact resolve eq103 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq103
  have eq229 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq238 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq229 X0 X1
       have i₂ := eq114 X1
       grind)
    | exact superpose eq114 eq229
    | (have j0 := eq229 X0 X1
       grind)
    | exact resolve eq229 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq577 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X0 X0))) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq238 X1 (τ X0)
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq238
    | (have j0 := eq238 X1 (τ X0)
       grind)
    | exact resolve eq238 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq238
  have eq626 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq577 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq577
    | (have j0 := eq577 X0 X1
       grind)
    | exact resolve eq577 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq628 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq626 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq626
    | (have j0 := eq626 X0 X1
       grind)
    | exact resolve eq626 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq629 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq628
    | (have j0 := eq628 X0 X1
       grind)
    | exact resolve eq628 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq630 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq629
    | (have j0 := eq629 X0 X1
       grind)
    | exact resolve eq629 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq631 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq630 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq630 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq630 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq632 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq631 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq631
    | (have j0 := eq631 X0 X1
       grind)
    | exact resolve eq631 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq633 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq632 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq632
    | exact resolve eq632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq632 (σ X1) X0
       grind)
    | exact superpose eq632 eq15
    | (have j1 := eq632 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq674 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq633 X0 (τ X1)
       grind)
    | exact superpose eq633 eq19
    | (have j1 := eq633 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq633
  have eq782 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq674 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq674
    | exact resolve eq674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq828 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq782 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq782
    | (have j0 := eq782 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq782 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq1188 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq640 x y
       grind)
    | exact superpose eq640 eq16
    | (have j1 := eq640 x y
       grind)
    | exact resolve eq16 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq1203 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1188
       have i₂ := eq828 y x
       grind)
    | exact superpose eq828 eq1188
    | (have j1 := eq828 (σ x) (σ y)
       grind)
    | (have r₁ := eq1188
       have r₂ := eq828 y x
       grind)
    | (have r₁ := eq1188
       have r₂ := eq828 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1188
       have r₂ := eq828 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1188 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828 eq1188
  have eq1204 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1203
  have eq1207 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1204
       grind)
    | exact superpose eq1204 eq16
    | exact resolve eq16 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1208 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1207
       have r₂ := eq114 x
       grind)
    | exact resolve eq1207 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1209 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1208
       grind)
    | exact superpose eq1208 eq16
    | exact resolve eq16 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1210 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1208
       grind)
    | exact superpose eq1208 eq10
    | exact resolve eq10 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1252 : x = y := by
    first
    | (have i₁ := eq1210
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1210
    | exact resolve eq1210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1253 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1209
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq1209
    | exact resolve eq1209 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1209
  have eq1254 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1253
       have i₂ := eq1252
       grind)
    | exact superpose eq1252 eq1253
    | exact resolve eq1253 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252 eq1253
  have eq1255 : False := by grind
  exact eq1255

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pxx_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq38
    | exact resolve eq38 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq38
  have eq60 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq60
    | (have j0 := eq60 X0 X1
       grind)
    | exact resolve eq60 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq65
    | exact resolve eq65 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq335 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq316 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq316
    | (have j0 := eq316 X0 X1
       grind)
    | exact resolve eq316 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq341 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq335 X0 X1
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq335 X1 X0
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq335 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq335 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq335
  have eq347 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq341 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq341
    | exact resolve eq341 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq341 (σ X1) X0
       grind)
    | exact superpose eq341 eq15
    | (have j1 := eq341 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq361 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq347 X0 (τ X1)
       grind)
    | exact superpose eq347 eq18
    | (have j1 := eq347 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq347
  have eq734 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq361
    | exact resolve eq361 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq769 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq734
    | (have j0 := eq734 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq734 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq1980 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq352 x y
       grind)
    | exact superpose eq352 eq16
    | (have j1 := eq352 x y
       grind)
    | exact resolve eq16 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq2054 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1980
       have i₂ := eq769 y x
       grind)
    | exact superpose eq769 eq1980
    | (have j1 := eq769 (σ x) (σ y)
       grind)
    | (have r₁ := eq1980
       have r₂ := eq769 y x
       grind)
    | (have r₁ := eq1980
       have r₂ := eq769 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1980
       have r₂ := eq769 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1980 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq1980
  have eq2055 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2054
  have eq2059 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2055
       grind)
    | exact superpose eq2055 eq10
    | exact resolve eq10 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055
  have eq2104 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2059
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2059
    | exact resolve eq2059 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq2105 : x = y := by grind
  clear eq2104
  have eq2397 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2105
       grind)
    | exact superpose eq2105 eq16
    | exact resolve eq16 eq2105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105
  have eq2398 : False := by grind
  exact eq2398

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_y_pxx_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
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
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq47
    | (have j0 := eq47 (M.op x y)
       grind)
    | exact resolve eq47 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
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
  have eq174 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq175 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X1 X2) X2) X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X1) (M.op (M.op X1 X2) X2) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) X1)) := by
    intro X0 X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq690 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq195 eq16
    | exact resolve eq16 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq785 : (M.op y x) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
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
  have eq787 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op (k X0 X1) X0)) = X2 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq893 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1925 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (M.op (M.op X1 X2) X2) x
       have i₂ := eq178 (M.op X0 (M.op (M.op X1 X2) X2)) X1 X2 x
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq6644 : ∀ X0 : G, y = (M.op (M.op x x) (M.op (M.op x X0) X0)) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq785
       grind)
    | exact superpose eq785 eq16
    | exact resolve eq16 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq6656 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6644 x
       have i₂ := eq16 x x x
       grind)
    | exact superpose eq16 eq6644
    | exact resolve eq6644 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6644
  have eq6686 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) X0) X0)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq787 eq16
    | exact resolve eq16 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq6698 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6686 x
       have i₂ := eq16 sF2 sF2 x
       grind)
    | exact superpose eq16 eq6686
    | exact resolve eq6686 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6686
  have eq6718 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq6656
       grind)
    | exact superpose eq6656 eq39
    | exact resolve eq39 eq6656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6719 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6718
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6718
    | exact resolve eq6718 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6718
  have eq6723 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq6719
    | exact resolve eq6719 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6719
  have eq6731 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq6723 eq6698
    | exact resolve eq6698 eq6723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6738 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq6731
       have r₂ := eq27
       grind)
    | exact resolve eq6731 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6731
  have eq6743 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq6738 eq175
    | (have r₁ := eq175
       have r₂ := eq6738
       grind)
    | exact resolve eq175 eq6738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq6744 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (M.op (σ y) X0) X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6738 eq177
    | exact resolve eq177 eq6738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq6738
  have eq6750 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq6743
  have eq6764 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq6750 eq6723
    | exact resolve eq6723 eq6750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6723
  have eq6767 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq6750 eq107
    | exact resolve eq107 eq6750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6750
  have eq6771 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq6764
  have eq6775 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq6767
    | exact resolve eq6767 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6767
  have eq6778 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq6775
       have r₂ := eq174
       grind)
    | exact resolve eq6775 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6775
  have eq6782 : x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6656
       have i₂ := eq6778
       grind)
    | exact superpose eq6778 eq6656
    | exact resolve eq6656 eq6778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6785 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq6778
       grind)
    | exact superpose eq6778 eq36
    | exact resolve eq36 eq6778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6778
  have eq6788 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6782
  have eq6791 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6785
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6785
    | exact resolve eq6785 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6785
  have eq6798 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6791 eq6698
    | exact resolve eq6698 eq6791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6698 eq6791
  have eq6803 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq6798
  have eq6812 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6771 eq31
    | exact resolve eq31 eq6771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6771
  have eq6882 : x = y ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq6812
    | exact resolve eq6812 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6812
  have eq6883 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq6882
  have eq6888 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6883 eq28
    | exact resolve eq28 eq6883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq6896 : (k y (M.op x y)) = (τ (k (σ y) (σ x))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6883 eq116
    | exact resolve eq116 eq6883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq6943 : (k y x) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq114 eq6896
    | exact resolve eq6896 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq6896
  have eq6951 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq6888
    | exact resolve eq6888 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6888
  have eq6959 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6656 eq6943
    | exact resolve eq6943 eq6656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6656 eq6943
  have eq6964 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq6951
       grind)
    | exact superpose eq6951 eq24
    | exact resolve eq24 eq6951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6968 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq6951
       grind)
    | exact superpose eq6951 eq176
    | exact resolve eq176 eq6951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7001 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq6964
    | exact resolve eq6964 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6964
  have eq7077 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6959 eq36
    | exact resolve eq36 eq6959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq6959
  have eq7081 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq7077
    | exact resolve eq7077 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7077
  have eq7085 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6883 eq7081
    | exact resolve eq7081 eq6883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6883 eq7081
  have eq7124 : (τ (σ x)) = (k y (τ (σ x))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7085 eq107
    | exact resolve eq107 eq7085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq7085
  have eq7132 : x = (k y x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq7124
    | exact resolve eq7124 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7124
  have eq7136 : x = (k y x) ∨ x = y := by
    first
    | (have r₁ := eq7132
       have r₂ := eq174
       grind)
    | exact resolve eq7132 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7132
  have eq7234 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq6803 eq27
    | exact resolve eq27 eq6803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6803
  have eq7248 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7001 eq7234
    | (have r₁ := eq7234
       have r₂ := eq7001
       grind)
    | exact resolve eq7234 eq7001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7001
  have eq7251 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq7248
  have eq7252 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq7251
  have eq7262 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7252 eq690
    | exact resolve eq690 eq7252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7267 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq7262
    | (have j0 := eq7262 X0
       grind)
    | exact resolve eq7262 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7262
  have eq7272 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7252 eq7267
    | exact resolve eq7267 eq7252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7252 eq7267
  have eq8181 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4, g5⟩ := hcon
    have f8181_17 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0)) ∨ x = (M.op x y) ∨ x = y := by
      intro X0
      grind
    have f8181_18 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
      intro X0
      grind
    have f8181_26 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
      intro X0 X1 X2
      grind
    have f8181_27 : x ≠ (M.op (M.op x y) (M.op x y)) := by grind
    have f8181_30 : (σ x) ≠ (σ y) := by grind
    have f8181_31 : x ≠ y := by grind
    have f8181_32 : x ≠ (M.op x y) := by grind
    have f8181_33 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ x = y ∨ x = (M.op x y) := by
      intro X0
      first
      | (have j0 := f8181_18 X0
         grind)
      | (have r₁ := f8181_18 X0
         have r₂ := f8181_30
         grind)
      | exact resolve f8181_18 f8181_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8181_34 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0)) ∨ x = y := by
      intro X0
      first
      | (have j0 := f8181_17 X0
         grind)
      | (have r₁ := f8181_17 X0
         have r₂ := f8181_32
         grind)
      | exact resolve f8181_17 f8181_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8181_35 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ x = (M.op x y) := by
      intro X0
      first
      | (have j0 := f8181_33 X0
         grind)
      | (have r₁ := f8181_33 X0
         have r₂ := f8181_31
         grind)
      | exact resolve f8181_33 f8181_31
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8181_36 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0)) := by
      intro X0
      first
      | (have j0 := f8181_34 X0
         grind)
      | (have r₁ := f8181_34 X0
         have r₂ := f8181_31
         grind)
      | exact resolve f8181_34 f8181_31
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8181_37 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 := by
      intro X0
      first
      | (have j0 := f8181_35 X0
         grind)
      | (have r₁ := f8181_35 X0
         have r₂ := f8181_32
         grind)
      | exact resolve f8181_35 f8181_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8181_49 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f8181_26 X1 X0 (σ x)
         have i₂ := f8181_37 X0
         grind)
      | exact superpose f8181_37 f8181_26
      | exact resolve f8181_26 f8181_37
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8181_62 : x = (M.op (M.op x y) (M.op x y)) := by
      first
      | (have i₁ := f8181_36 x
         have i₂ := f8181_49 x (M.op x y)
         grind)
      | exact superpose f8181_49 f8181_36
      | exact resolve f8181_36 f8181_49
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8181_71 : False := by
      first
      | (have r₁ := f8181_62
         have r₂ := f8181_27
         grind)
      | exact resolve f8181_62 f8181_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f8181_71
  clear eq6968 eq7272
  have eq8197 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8181
  have eq8808 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = X0 ∨ (M.op y x) = (M.op x x) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq789 y x X0
       have i₂ := eq7136
       grind)
    | exact superpose eq7136 eq789
    | (have j0 := eq789 y x x
       grind)
    | exact resolve eq789 eq7136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq7136
  have eq8861 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = X0 ∨ (M.op y x) = (M.op x x) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8808 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8808
    | (have j0 := eq8808 X0
       grind)
    | exact resolve eq8808 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8808
  have eq8895 : ∀ X0 : G, y = (M.op x y) ∨ (M.op (M.op X0 x) (M.op x y)) = X0 ∨ (M.op y x) = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8861 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8861
    | (have j0 := eq8861 X0
       grind)
    | exact resolve eq8861 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8861
  have eq8915 : ∀ X0 : G, y = (M.op x y) ∨ (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ (M.op y x) = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq6951 eq8895
    | exact resolve eq8895 eq6951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8895
  have eq8931 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq6951 eq8915
    | (have j0 := eq8915 X0
       grind)
    | exact resolve eq8915 eq6951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8915
  have eq13772 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op x y) X0) X0)) ∨ (M.op (M.op X1 (M.op x y)) (M.op x y)) = X1 ∨ y = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq8931 (M.op X0 X1)
       grind)
    | exact superpose eq8931 eq16
    | (have j1 := eq8931 X1
       grind)
    | exact resolve eq16 eq8931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8931
  have eq13793 : ∀ X1 : G, y = (M.op x y) ∨ (M.op (M.op X1 (M.op x y)) (M.op x y)) = X1 ∨ y = (M.op x y) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq13772 x X1
       have i₂ := eq16 sF0 sF0 x
       grind)
    | exact superpose eq16 eq13772
    | (have j0 := eq13772 x X1
       grind)
    | exact resolve eq13772 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13772
  have eq13794 : ∀ X1 : G, (M.op (M.op X1 (M.op x y)) (M.op x y)) = X1 ∨ y = (M.op x y) ∨ x = y := by
    intro X1
    first
    | (have j0 := eq13793 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13793
  have eq13820 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 ∨ y = (M.op x y) ∨ x = y := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f13820_14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1) = X0 := by
      intro X0 X1 X2
      grind
    have f13820_15 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ y = (M.op x y) ∨ x = y := by
      intro X0
      grind
    have f13820_24 : X1 ≠ (M.op (M.op X1 X0) X0) := by grind
    have f13820_25 : y ≠ (M.op x y) := by grind
    have f13820_26 : x ≠ y := by grind
    have f13820_27 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ x = y := by
      intro X0
      first
      | (have j0 := f13820_15 X0
         grind)
      | (have r₁ := f13820_15 X0
         have r₂ := f13820_25
         grind)
      | exact resolve f13820_15 f13820_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f13820_28 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 := by
      intro X0
      first
      | (have j0 := f13820_27 X0
         grind)
      | (have r₁ := f13820_27 X0
         have r₂ := f13820_26
         grind)
      | exact resolve f13820_27 f13820_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f13820_62 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f13820_14 X1 X0 (M.op x y)
         have i₂ := f13820_28 X0
         grind)
      | exact superpose f13820_28 f13820_14
      | exact resolve f13820_14 f13820_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f13820_69 : X1 ≠ X1 := by
      first
      | (have i₁ := f13820_24
         have i₂ := f13820_62 X0 X1
         grind)
      | exact superpose f13820_62 f13820_24
      | (have r₁ := f13820_24
         have r₂ := f13820_62 X0 X1
         grind)
      | exact resolve f13820_24 f13820_62
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f13820_77 : False := by grind
    exact f13820_77
  have eq13826 : x = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13794 eq176
    | exact resolve eq176 eq13794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13834 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13794 eq6744
    | exact resolve eq6744 eq13794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6744 eq13794
  have eq13856 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq13834
  have eq13873 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6951 eq13826
    | exact resolve eq13826 eq6951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6951 eq13826
  have eq13996 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ y = (M.op x y) ∨ x = y ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13820 X0 X0
       have i₂ := eq893 X0
       grind)
    | exact superpose eq893 eq13820
    | (have j1 := eq893 X0
       grind)
    | exact resolve eq13820 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13820
  have eq14288 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq13856 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq13856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13856
  have eq14307 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq14288
  have eq14308 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq14307
  have eq14376 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq14308 eq115
    | exact resolve eq115 eq14308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq14308
  have eq14382 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq14376
    | exact resolve eq14376 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14376
  have eq14385 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq6788 eq14382
    | exact resolve eq14382 eq6788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6788 eq14382
  have eq15770 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13996 y
       have i₂ := eq14385
       grind)
    | exact superpose eq14385 eq13996
    | (have j0 := eq13996 y
       grind)
    | exact resolve eq13996 eq14385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13996
  have eq15891 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq15770
  have eq15941 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13873 eq15891
    | exact resolve eq15891 eq13873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13873 eq15891
  have eq15942 : y = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq15941
  have eq16004 : y ≠ y ∨ y = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq15942
       grind)
    | exact superpose eq15942 eq13
    | (have j0 := eq13 y y
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq15942
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15942
       grind)
    | exact resolve eq13 eq15942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15942
  have eq16023 : y = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq16004
  have eq16036 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14385 eq16023
    | exact resolve eq16023 eq14385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14385 eq16023
  have eq16037 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq16036
  have eq16052 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq16037 eq31
    | exact resolve eq31 eq16037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16037
  have eq16141 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq16052
    | exact resolve eq16052 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16052
  have eq16142 : y = (M.op x y) ∨ x = y := by grind
  clear eq16141
  have eq16175 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq16142
       grind)
    | exact superpose eq16142 eq18
    | exact resolve eq18 eq16142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16176 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq16142
       grind)
    | exact superpose eq16142 eq24
    | exact resolve eq24 eq16142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16180 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq16142
       grind)
    | exact superpose eq16142 eq176
    | exact resolve eq176 eq16142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq16198 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq16142
  have eq16213 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq16176
    | exact resolve eq16176 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16176
  have eq16407 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq16213 eq7234
    | (have r₁ := eq7234
       have r₂ := eq16213
       grind)
    | exact resolve eq7234 eq16213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7234
  have eq16410 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq16407
  have eq16411 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16410
  have eq16524 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16411 eq690
    | exact resolve eq690 eq16411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq16535 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26 eq16524
    | (have j0 := eq16524 X0
       grind)
    | exact resolve eq16524 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16524
  have eq16540 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16411 eq16535
    | exact resolve eq16535 eq16411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16535
  have eq16686 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq8197 eq16180
    | exact resolve eq16180 eq8197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8197 eq16180
  have eq16776 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq16686
  have eq16799 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16776
       have r₂ := eq16198
       grind)
    | exact resolve eq16776 eq16198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16776
  have eq16803 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16175 eq16799
    | exact resolve eq16799 eq16175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16799
  have eq16841 : ∀ X0 : G, (M.op (M.op X0 (M.op x (M.op x y))) (M.op x y)) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq16803 eq1925
    | exact resolve eq1925 eq16803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16866 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq16175 eq16841
    | exact resolve eq16841 eq16175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16175 eq16841
  have eq17484 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq16540 eq1925
    | exact resolve eq1925 eq16540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925 eq16540
  have eq17586 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq16866 sF0
       have i₂ := eq893 sF0
       grind)
    | exact superpose eq893 eq16866
    | (have j1 := eq893 (M.op x y)
       grind)
    | exact resolve eq16866 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16866
  have eq17681 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16803 eq17586
    | exact resolve eq17586 eq16803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17586
  have eq17690 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17681
       have r₂ := eq16198
       grind)
    | exact resolve eq17681 eq16198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16198 eq17681
  have eq17822 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17484 X0 X0
       have i₂ := eq893 X0
       grind)
    | exact superpose eq893 eq17484
    | (have j1 := eq893 X0
       grind)
    | exact resolve eq17484 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq18213 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17690 eq17484
    | exact resolve eq17484 eq17690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17484 eq17690
  have eq18214 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18213
  have eq18225 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16803 eq18214
    | exact resolve eq18214 eq16803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16803 eq18214
  have eq18280 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18225 eq41
    | exact resolve eq41 eq18225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq18225
  have eq18293 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq18280
    | exact resolve eq18280 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18280
  have eq18302 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18293
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18293
    | exact resolve eq18293 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18293
  have eq18307 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16213 eq18302
    | exact resolve eq18302 eq16213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16213 eq18302
  have eq24166 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18307 eq17822
    | (have j0 := eq17822 (σ y)
       grind)
    | exact resolve eq17822 eq18307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17822
  have eq24341 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq24166
  have eq24412 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq24341
    | exact resolve eq24341 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24341
  have eq24456 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq16411 eq24412
    | exact resolve eq24412 eq16411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16411 eq24412
  have eq24457 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq24456
  have eq24513 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq24457 eq13
    | (have j0 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq24457
       grind)
    | exact resolve eq13 eq24457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24457
  have eq24536 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq24513
  have eq24561 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18307 eq24536
    | exact resolve eq24536 eq18307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18307 eq24536
  have eq24562 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq24561
  have eq24579 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq24562 eq31
    | exact resolve eq31 eq24562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq24562
  have eq24668 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq24579
    | exact resolve eq24579 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24579
  have eq24669 : x = y := by grind
  clear eq24668
  have eq24706 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24669
       grind)
    | exact superpose eq24669 eq18
    | exact resolve eq18 eq24669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24707 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq24669
       grind)
    | exact superpose eq24669 eq24
    | exact resolve eq24 eq24669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq24710 : x ≠ (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq174
       have i₂ := eq24669
       grind)
    | exact superpose eq24669 eq174
    | exact resolve eq174 eq24669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq24669
  have eq24743 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24707
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24707
    | exact resolve eq24707 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24707
  have eq24747 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq24743 eq26
    | exact resolve eq26 eq24743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq24743
  have eq24857 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq24706
       grind)
    | exact superpose eq24706 eq12
    | exact resolve eq12 eq24706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24706
  have eq24877 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq24857
  have eq24913 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq24747 eq12
    | exact resolve eq12 eq24747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24914 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq24747 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq13 eq24747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24747
  have eq24933 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24913
  have eq25156 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq24877
       grind)
    | exact superpose eq24877 eq39
    | exact resolve eq39 eq24877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq24877
  have eq25172 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25156
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25156
    | exact resolve eq25156 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25156
  have eq25176 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq25172
    | exact resolve eq25172 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25172
  have eq25220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25176 eq24933
    | exact resolve eq24933 eq25176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25231 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25220
       have r₂ := eq27
       grind)
    | exact resolve eq25220 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25220
  have eq25238 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25231 eq27
    | exact resolve eq27 eq25231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25254 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25231 eq24914
    | (have r₁ := eq24914
       have r₂ := eq25231
       grind)
    | exact resolve eq24914 eq25231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24914 eq25231
  have eq25255 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq25254
  have eq25299 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25255 eq25176
    | exact resolve eq25176 eq25255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25176
  have eq25301 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25255 eq141
    | exact resolve eq141 eq25255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq25255
  have eq25308 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq25299
  have eq25315 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq25301
    | exact resolve eq25301 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25301
  have eq25317 : x = (M.op x y) := by
    first
    | (have r₁ := eq25308
       have r₂ := eq25238
       grind)
    | exact resolve eq25308 eq25238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25238 eq25308
  have eq25321 : x = (k x x) := by
    first
    | (have r₁ := eq25315
       have r₂ := eq24710
       grind)
    | exact resolve eq25315 eq24710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24710 eq25315
  have eq25324 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq25321
       have i₂ := eq25317
       grind)
    | exact superpose eq25317 eq25321
    | exact resolve eq25321 eq25317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25321
  have eq25328 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq25317
       grind)
    | exact superpose eq25317 eq22
    | exact resolve eq22 eq25317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq25317
  have eq25525 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq25328 eq20
    | exact resolve eq20 eq25328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25328
  have eq26649 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq25324 eq37
    | exact resolve eq37 eq25324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq25324
  have eq26663 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq26649
    | exact resolve eq26649 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq26649
  have eq26667 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq25525 eq26663
    | exact resolve eq26663 eq25525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26663
  have eq26761 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26667 eq24933
    | exact resolve eq24933 eq26667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24933 eq26667
  have eq26771 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26761
  have eq26784 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq26771 eq27
    | exact resolve eq27 eq26771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq26771
  have eq26813 : False := by grind
  exact eq26813

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pxx_pyy_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq66 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq92 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq101 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq109 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq112 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq112 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq112 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq113 (σ X0)
       grind)
    | exact superpose eq113 eq10
    | exact resolve eq10 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq43
    | exact resolve eq43 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq117 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq75
    | exact resolve eq75 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq118 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq49
    | exact resolve eq49 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq119 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq118
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq118
    | exact resolve eq118 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq120 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq113 sF3
       grind)
    | exact superpose eq113 eq117
    | exact resolve eq117 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq121 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq116
    | exact resolve eq116 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq122 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq115 X0
       have i₂ := eq113 X0
       grind)
    | exact superpose eq113 eq115
    | exact resolve eq115 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq129 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq101
       have i₂ := eq113 sF3
       grind)
    | exact superpose eq113 eq101
    | exact resolve eq101 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq130 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq129
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq129
    | exact resolve eq129 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq129
  have eq936 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq122 X1
       grind)
    | exact superpose eq122 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq122
  have eq1024 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (M.op (σ X0) X2) X2)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X1) (σ X0) X2
       have i₂ := eq936 X0 X1
       grind)
    | exact superpose eq936 eq14
    | (have j1 := eq936 X0 X1
       grind)
    | exact resolve eq14 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq9984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq9984
    | exact resolve eq9984 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9984
  have eq9996 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq9985
       have r₂ := eq27
       grind)
    | exact resolve eq9985 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9985
  have eq10000 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq9996
    | exact resolve eq9996 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9996
  have eq10002 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq10000
    | exact resolve eq10000 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10000
  have eq10004 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10002 eq109
    | (have r₁ := eq109
       have r₂ := eq10002
       grind)
    | exact resolve eq109 eq10002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10002
  have eq10037 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq10004
  have eq10038 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq10037
  have eq10046 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10038 eq96
    | exact resolve eq96 eq10038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq10038
  have eq10054 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10046
  have eq10056 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10054
       have r₂ := eq27
       grind)
    | exact resolve eq10054 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10054
  have eq10058 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq10056
       grind)
    | exact superpose eq10056 eq108
    | (have r₁ := eq108
       have r₂ := eq10056
       grind)
    | exact resolve eq108 eq10056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10059 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq10056
       grind)
    | exact superpose eq10056 eq121
    | exact resolve eq121 eq10056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10056
  have eq10091 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10058
  have eq10092 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10091
  have eq10101 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10059
    | exact resolve eq10059 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10059
  have eq10105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq10092
       grind)
    | exact superpose eq10092 eq74
    | exact resolve eq74 eq10092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10092
  have eq10119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10105
    | exact resolve eq10105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10105
  have eq10183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10119 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10119
  have eq10186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10183
    | exact resolve eq10183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10183
  have eq10197 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10186
       have r₂ := eq27
       grind)
    | exact resolve eq10186 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10186
  have eq10201 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10197
    | exact resolve eq10197 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10197
  have eq10203 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq10201
    | exact resolve eq10201 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10201
  have eq10204 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10203
  have eq10217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10204 eq10101
    | exact resolve eq10101 eq10204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10101 eq10204
  have eq10242 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10217
  have eq10248 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10242
       have r₂ := eq27
       grind)
    | exact resolve eq10242 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10242
  have eq10253 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10248 eq66
    | (have r₁ := eq66
       have r₂ := eq10248
       grind)
    | exact resolve eq66 eq10248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq10248
  have eq10264 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10253
  have eq10454 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10264 eq92
    | exact resolve eq92 eq10264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq10264
  have eq10478 : (k y x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130 eq10454
    | exact resolve eq10454 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq10454
  have eq10481 : (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq10478
       have r₂ := eq65
       grind)
    | exact resolve eq10478 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq10478
  have eq10487 : (k (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq10481
       grind)
    | exact superpose eq10481 eq74
    | exact resolve eq74 eq10481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10495 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq10481
       grind)
    | exact superpose eq10481 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq10481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10496 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10495
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10495
    | exact resolve eq10495 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10495
  have eq10503 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq10487
       have i₂ := eq120
       grind)
    | exact superpose eq120 eq10487
    | exact resolve eq10487 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq10487
  have eq10505 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10496
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10496
    | exact resolve eq10496 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10496
  have eq10507 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10505
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10505
    | exact resolve eq10505 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10505
  have eq12424 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq10507
       grind)
    | exact superpose eq10507 eq14
    | exact resolve eq14 eq10507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10507
  have eq12447 : (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq50 eq12424
    | exact resolve eq12424 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12424
  have eq12459 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq12447
       grind)
    | exact superpose eq12447 eq108
    | (have r₁ := eq108
       have r₂ := eq12447
       grind)
    | exact resolve eq108 eq12447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq12447
  have eq12495 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq12459
  have eq12496 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq12495
  have eq12507 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12496
       have i₂ := eq10481
       grind)
    | exact superpose eq10481 eq12496
    | exact resolve eq12496 eq10481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10481 eq12496
  have eq13115 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq12507
       grind)
    | exact superpose eq12507 eq14
    | exact resolve eq14 eq12507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12507
  have eq13138 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq50 eq13115
    | exact resolve eq13115 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq13115
  have eq13139 : y = (M.op x y) ∨ x = y := by grind
  clear eq13138
  have eq13151 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq13139 eq20
    | exact resolve eq20 eq13139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13266 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13151
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13151
    | exact resolve eq13151 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13151
  have eq15224 : ∀ X0 : G, (σ x) = (M.op (k (σ y) (σ x)) (M.op (M.op (σ y) X0) X0)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1024 y x X0
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq1024
    | (have j0 := eq1024 y x x
       grind)
    | exact resolve eq1024 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1024
  have eq15487 : ∀ X0 : G, (σ x) = (M.op (k (σ y) (σ x)) (M.op (M.op (σ y) X0) X0)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15224 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15224
    | (have j0 := eq15224 X0
       grind)
    | exact resolve eq15224 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15224
  have eq15613 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) X0) X0)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10503 eq15487
    | exact resolve eq15487 eq10503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15487
  have eq15718 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15613 x
       have i₂ := eq14 sF3 sF3 x
       grind)
    | exact superpose eq14 eq15613
    | exact resolve eq15613 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15613
  have eq15823 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15718
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15718
    | exact resolve eq15718 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15718
  have eq15916 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15823
       have i₂ := eq121
       grind)
    | exact superpose eq121 eq15823
    | exact resolve eq15823 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq15823
  have eq16002 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15916
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15916
    | exact resolve eq15916 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15916
  have eq16077 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16002
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16002
    | exact resolve eq16002 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16002
  have eq16128 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16077
    | exact resolve eq16077 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16077
  have eq16148 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16128
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16128
    | exact resolve eq16128 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16128
  have eq16157 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16148
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16148
    | exact resolve eq16148 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16148
  have eq16166 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq16157
    | exact resolve eq16157 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16157
  have eq16172 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16166 eq109
    | (have r₁ := eq109
       have r₂ := eq16166
       grind)
    | exact resolve eq109 eq16166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq16166
  have eq16221 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq16172
  have eq16222 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq16221
  have eq16227 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10503 eq16222
    | exact resolve eq16222 eq10503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10503 eq16222
  have eq16259 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq16227 eq14
    | exact resolve eq14 eq16227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16227
  have eq16283 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq51 eq16259
    | exact resolve eq16259 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq16259
  have eq16284 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq16283
  have eq16288 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16284 eq27
    | exact resolve eq27 eq16284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16284
  have eq17452 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq13266 eq16288
    | (have r₁ := eq16288
       have r₂ := eq13266
       grind)
    | exact resolve eq16288 eq13266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13266 eq16288
  have eq17453 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq17452
  have eq17455 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq17453 eq28
    | exact resolve eq28 eq17453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq17453
  have eq17597 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq17455
    | exact resolve eq17455 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17455
  have eq17689 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq17597 eq13139
    | exact resolve eq13139 eq17597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13139 eq17597
  have eq17708 : x = y := by grind
  clear eq17689
  have eq17924 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq17708
       grind)
    | exact superpose eq17708 eq18
    | exact resolve eq18 eq17708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq17925 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq17708
       grind)
    | exact superpose eq17708 eq24
    | exact resolve eq24 eq17708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq17708
  have eq18050 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17925
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17925
    | exact resolve eq17925 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17925
  have eq18075 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18050 eq26
    | exact resolve eq26 eq18050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq18050
  have eq18358 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq18075 eq119
    | exact resolve eq119 eq18075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq18075
  have eq18428 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18358
       have i₂ := eq17924
       grind)
    | exact superpose eq17924 eq18358
    | exact resolve eq18358 eq17924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17924 eq18358
  have eq18449 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18428 eq15
    | exact resolve eq15 eq18428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18428
  have eq18493 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq18449
    | exact resolve eq18449 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq18449
  have eq18504 : False := by grind
  exact eq18504

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pxx_y_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X1 X2) X2) X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X1) (M.op (M.op X1 X2) X2) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq181 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) := by
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
  have eq789 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq806 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq808 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op (M.op X0 X2) X2)) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq872 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq918 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq806
       grind)
    | exact superpose eq806 eq39
    | exact resolve eq39 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq919 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq918
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq918
    | exact resolve eq918 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq921 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq919
    | exact resolve eq919 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq929 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq921 eq808
    | exact resolve eq808 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq929
       have r₂ := eq27
       grind)
    | exact resolve eq929 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq940 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq936 eq27
    | exact resolve eq27 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq943 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq936 eq181
    | (have r₁ := eq181
       have r₂ := eq936
       grind)
    | exact resolve eq181 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq949 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq943
  have eq951 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq921 eq949
    | exact resolve eq949 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq957 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq951 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq962 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq957
  have eq964 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq962
       have r₂ := eq940
       grind)
    | exact resolve eq962 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940 eq962
  have eq967 : (τ (σ (M.op x y))) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq964 eq115
    | exact resolve eq115 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq964
  have eq972 : (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq967
    | exact resolve eq967 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq967
  have eq1773 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (M.op (M.op X1 X2) X2) x
       have i₂ := eq176 (M.op X0 (M.op (M.op X1 X2) X2)) X1 X2 x
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq8204 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq813 y y X0
       have i₂ := eq972
       grind)
    | exact superpose eq972 eq813
    | (have j0 := eq813 y y x
       grind)
    | exact resolve eq813 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8340 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8204 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8204
  have eq8414 : y = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq174 eq8340
    | exact resolve eq8340 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8340
  have eq8476 : y ≠ y ∨ y = (k y y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq8414
       grind)
    | exact superpose eq8414 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq8414
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8414
       grind)
    | exact resolve eq13 eq8414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8414
  have eq8484 : y = (k y y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq8476
  have eq8490 : y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq972 eq8484
    | exact resolve eq8484 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8484
  have eq8491 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8490
  have eq8495 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8491 eq27
    | exact resolve eq27 eq8491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8503 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8491 eq789
    | (have r₁ := eq789
       have r₂ := eq8491
       grind)
    | exact resolve eq789 eq8491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8491
  have eq8504 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8503
  have eq9080 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8504 eq921
    | exact resolve eq921 eq8504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq9083 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8504 eq107
    | exact resolve eq107 eq8504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8504
  have eq9092 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq9080
  have eq9098 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq9083
    | exact resolve eq9083 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9083
  have eq9100 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq9092
       have r₂ := eq8495
       grind)
    | exact resolve eq9092 eq8495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8495 eq9092
  have eq9104 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq9098
       have r₂ := eq787
       grind)
    | exact resolve eq9098 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9098
  have eq9107 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq9100 eq9104
    | exact resolve eq9104 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9104
  have eq9111 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq9100 eq31
    | exact resolve eq31 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9267 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq9111
    | exact resolve eq9111 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9111
  have eq9268 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq9267
  have eq9276 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq9268
       grind)
    | exact superpose eq9268 eq24
    | exact resolve eq24 eq9268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9281 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq180
       have i₂ := eq9268
       grind)
    | exact superpose eq9268 eq180
    | (have r₁ := eq180
       have r₂ := eq9268
       grind)
    | exact resolve eq180 eq9268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq9268
  have eq9287 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq9281
  have eq9292 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq9276
    | exact resolve eq9276 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9276
  have eq9458 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9287 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq9287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9460 : (M.op x y) ≠ (k (M.op x y) x) ∨ (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9287 eq13
    | exact resolve eq13 eq9287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9287
  have eq9470 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq9458
  have eq9474 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9470
       have r₂ := eq9460
       grind)
    | exact resolve eq9470 eq9460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9460 eq9470
  have eq9477 : (k (σ (M.op x y)) (σ x)) = (σ (k (M.op x y) (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9474 eq39
    | exact resolve eq39 eq9474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9474
  have eq9485 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq41 eq9477
    | exact resolve eq9477 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq9477
  have eq9487 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq9485
    | exact resolve eq9485 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9485
  have eq9489 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9292 eq9487
    | exact resolve eq9487 eq9292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9487
  have eq9497 : ∀ X0 : G, (σ y) = (M.op (k (σ y) (σ x)) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9489 eq813
    | (have j0 := eq813 (σ y) (σ y) x
       grind)
    | exact resolve eq813 eq9489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9505 : ∀ X0 : G, (σ y) = (M.op (k (σ y) (σ x)) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq9497 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9497
  have eq9518 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq9107 eq36
    | exact resolve eq36 eq9107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9107
  have eq9529 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq9518
    | exact resolve eq9518 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9518
  have eq9555 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq9529 eq872
    | (have j0 := eq872 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq872 (σ (M.op x y)) (σ y)
       have r₂ := eq9529
       grind)
    | exact resolve eq872 eq9529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq9556 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq9555
  have eq13460 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq9556 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ y) (σ (M.op x y))
       have r₂ := eq9556
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq9556
       grind)
    | exact resolve eq13 eq9556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13479 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq13460
  have eq13528 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq9529 eq13479
    | exact resolve eq13479 eq9529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9529 eq13479
  have eq14486 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ (M.op x y)) (σ y))) (σ y)) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13528 eq1773
    | exact resolve eq1773 eq13528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13528
  have eq14514 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9556 eq14486
    | exact resolve eq14486 eq9556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9556 eq14486
  have eq18911 : x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq14514 eq174
    | exact resolve eq174 eq14514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14514
  have eq19025 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq9100 eq18911
    | exact resolve eq18911 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18911
  have eq19095 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ (M.op x y)) (σ y))) (σ (M.op x y))) = X0 ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19025 eq1773
    | exact resolve eq1773 eq19025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19155 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) = X0 ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19025 eq19095
    | exact resolve eq19095 eq19025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19025 eq19095
  have eq23383 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq19155 eq174
    | exact resolve eq174 eq19155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19155
  have eq23491 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq9100 eq23383
    | exact resolve eq23383 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23383
  have eq23492 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq23491
  have eq23539 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op x y) y)) (M.op x y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23492 eq1773
    | exact resolve eq1773 eq23492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1773
  have eq23568 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23492 eq23539
    | exact resolve eq23539 eq23492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23492 eq23539
  have eq23634 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq23568 eq175
    | exact resolve eq175 eq23568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23568
  have eq23746 : (σ x) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq23634 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq23634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23634
  have eq23774 : (σ x) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq23746
  have eq24464 : (τ (σ x)) = (k y (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq23774 eq107
    | exact resolve eq107 eq23774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq23774
  have eq24473 : x = (k y (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq24464
    | exact resolve eq24464 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24464
  have eq24474 : (M.op x y) = (k y (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq9100 eq24473
    | exact resolve eq24473 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9100 eq24473
  have eq32373 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq808 eq9505
    | exact resolve eq9505 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32654 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq175 eq32373
    | exact resolve eq32373 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32373
  have eq32661 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq936 eq32654
    | exact resolve eq32654 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32654
  have eq32662 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32661
  have eq32704 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32662 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq32662
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq32662
       grind)
    | exact resolve eq13 eq32662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32662
  have eq32740 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32704
  have eq32823 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32740 eq9489
    | exact resolve eq9489 eq32740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32740
  have eq32845 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32823
  have eq32856 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq936 eq32845
    | exact resolve eq32845 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32845
  have eq32857 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32856
  have eq32967 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32857 eq808
    | exact resolve eq808 eq32857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32857
  have eq33000 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq32967
  have eq33020 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33000 eq27
    | exact resolve eq27 eq33000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33000
  have eq33067 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9292 eq33020
    | (have r₁ := eq33020
       have r₂ := eq9292
       grind)
    | exact resolve eq33020 eq9292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9292 eq33020
  have eq33068 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq33067
  have eq33069 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq33068
  have eq33074 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op (σ y) X0) X0)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq33069 eq175
    | exact resolve eq175 eq33069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq33081 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq33069 eq789
    | (have r₁ := eq789
       have r₂ := eq33069
       grind)
    | exact resolve eq789 eq33069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq33069
  have eq33102 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq33081
  have eq33103 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq33102
  have eq33135 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq33103 eq9505
    | exact resolve eq9505 eq33103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9505
  have eq33156 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq33135 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33135
  have eq33170 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33074 eq33156
    | exact resolve eq33156 eq33074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33074 eq33156
  have eq33171 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq33170
  have eq33219 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq33171 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq33171
       grind)
    | exact resolve eq13 eq33171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33171
  have eq33255 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq33219
  have eq33430 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq33255 eq9489
    | exact resolve eq9489 eq33255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9489 eq33255
  have eq33452 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq33430
  have eq33462 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33103 eq33452
    | exact resolve eq33452 eq33103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33103 eq33452
  have eq33463 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq33462
  have eq33470 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq33463 eq31
    | exact resolve eq31 eq33463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33463
  have eq33655 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq33470
    | exact resolve eq33470 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq33470
  have eq33656 : x = (M.op x y) ∨ x = y := by grind
  clear eq33655
  have eq33675 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq33656
       grind)
    | exact superpose eq33656 eq22
    | exact resolve eq22 eq33656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33683 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq787
       have i₂ := eq33656
       grind)
    | exact superpose eq33656 eq787
    | (have r₁ := eq787
       have r₂ := eq33656
       grind)
    | exact resolve eq787 eq33656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq33687 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq33683
  have eq33691 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq33675
    | exact resolve eq33675 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33675
  have eq34820 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq33687 eq36
    | exact resolve eq36 eq33687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq33687
  have eq34833 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq34820
    | exact resolve eq34820 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34820
  have eq34835 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq33691 eq34833
    | exact resolve eq34833 eq33691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34833
  have eq34844 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq34835 eq808
    | exact resolve eq808 eq34835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34835
  have eq34873 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq34844
  have eq34888 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq936 eq34873
    | exact resolve eq34873 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq34873
  have eq34889 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq34888
  have eq34926 : (M.op x y) = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34889 eq24474
    | exact resolve eq24474 eq34889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24474
  have eq34930 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq34889
  have eq34932 : (M.op x y) = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34926
  have eq34948 : (M.op x y) = (k y (τ (σ y))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq34932
       have r₂ := eq34930
       grind)
    | exact resolve eq34932 eq34930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34930 eq34932
  have eq34954 : (M.op x y) = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq34948
    | exact resolve eq34948 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq34948
  have eq34956 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq972 eq34954
    | exact resolve eq34954 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972 eq34954
  have eq34957 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34956
  have eq34975 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq813 y y X0
       have i₂ := eq34957
       grind)
    | exact superpose eq34957 eq813
    | (have j0 := eq813 y y x
       grind)
    | exact resolve eq813 eq34957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq34983 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq34975 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34975
  have eq34990 : y = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq174 eq34983
    | exact resolve eq34983 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq34983
  have eq38195 : y ≠ y ∨ y = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq34990
       grind)
    | exact superpose eq34990 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq34990
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq34990
       grind)
    | exact resolve eq13 eq34990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34990
  have eq38235 : y = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq38195
  have eq38253 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34957 eq38235
    | exact resolve eq38235 eq34957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34957 eq38235
  have eq38254 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq38253
  have eq38269 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq38254 eq27
    | exact resolve eq27 eq38254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38254
  have eq38321 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq38269
       have r₂ := eq33691
       grind)
    | exact resolve eq38269 eq33691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33691 eq38269
  have eq38344 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq38321
  have eq38347 : x = y := by
    first
    | (have r₁ := eq38344
       have r₂ := eq33656
       grind)
    | exact resolve eq38344 eq33656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33656 eq38344
  have eq38361 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq38347
       grind)
    | exact superpose eq38347 eq18
    | exact resolve eq18 eq38347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq38362 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38347
       grind)
    | exact superpose eq38347 eq24
    | exact resolve eq24 eq38347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq38372 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq806
       have i₂ := eq38347
       grind)
    | exact superpose eq38347 eq806
    | exact resolve eq806 eq38347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806 eq38347
  have eq38393 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq38372
  have eq38400 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq38362
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38362
    | exact resolve eq38362 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38362
  have eq38404 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq38400 eq26
    | exact resolve eq26 eq38400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq38425 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38400 eq808
    | exact resolve eq808 eq38400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq38400
  have eq38516 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq38425
  have eq38657 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq38361
       grind)
    | exact superpose eq38361 eq13
    | exact resolve eq13 eq38361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38361
  have eq38690 : (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq38657
       have r₂ := eq38393
       grind)
    | exact resolve eq38657 eq38393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38393 eq38657
  have eq38726 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq38404 eq13
    | exact resolve eq13 eq38404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38404
  have eq38760 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq38726
       have r₂ := eq38516
       grind)
    | exact resolve eq38726 eq38516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38516 eq38726
  have eq38771 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq38690
       grind)
    | exact superpose eq38690 eq39
    | exact resolve eq39 eq38690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq38690
  have eq38784 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq38771
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38771
    | exact resolve eq38771 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq38771
  have eq38787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38760 eq38784
    | exact resolve eq38784 eq38760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38760 eq38784
  have eq38789 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq38787
    | exact resolve eq38787 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq38787
  have eq38791 : False := by grind
  exact eq38791
