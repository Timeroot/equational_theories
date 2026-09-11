import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq216 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq380 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq388 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq380 X0
       grind)
    | exact superpose eq380 eq14
    | exact resolve eq14 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq706 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq872 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq388
    | exact resolve eq388 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq388
    | exact resolve eq388 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq876 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq388
    | exact resolve eq388 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq388
  have eq8156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8156
    | exact resolve eq8156 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8156
  have eq8168 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq8157
       have r₂ := eq28
       grind)
    | exact resolve eq8157 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8157
  have eq8170 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8168
    | exact resolve eq8168 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8168
  have eq8190 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq8170
  have eq8212 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8190
    | exact resolve eq8190 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8190
  have eq9965 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8212 eq97
    | exact resolve eq97 eq8212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8212
  have eq9975 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9965
  have eq9978 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9975
       have r₂ := eq28
       grind)
    | exact resolve eq9975 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9975
  have eq9999 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9978
  have eq10033 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9999
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9999
    | exact resolve eq9999 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9999
  have eq10610 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq10033
       grind)
    | exact superpose eq10033 eq72
    | exact resolve eq72 eq10033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq10033
  have eq10624 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq10610
    | exact resolve eq10610 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10610
  have eq10770 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10624 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10770
    | exact resolve eq10770 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10770
  have eq10784 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10773
       have r₂ := eq28
       grind)
    | exact resolve eq10773 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10773
  have eq10786 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10784
    | exact resolve eq10784 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10784
  have eq10787 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10786
  have eq10812 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10787
  have eq10854 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq10812
    | exact resolve eq10812 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10812
  have eq10944 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10854 eq10624
    | exact resolve eq10624 eq10854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10624 eq10854
  have eq10946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10944
  have eq10952 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10946
       have r₂ := eq28
       grind)
    | exact resolve eq10946 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10946
  have eq11527 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10952 eq216
    | exact resolve eq216 eq10952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq11548 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10952 eq876
    | exact resolve eq876 eq10952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12313 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11548 eq11527
    | exact resolve eq11527 eq11548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11527 eq11548
  have eq12361 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12313
  have eq12364 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12361
    | exact resolve eq12361 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12361
  have eq12367 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12364 eq28
    | exact resolve eq28 eq12364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12399 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12364 eq10952
    | exact resolve eq10952 eq12364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10952
  have eq12402 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq12399
  have eq13108 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12402 eq27
    | exact resolve eq27 eq12402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13109 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12402 eq30
    | exact resolve eq30 eq12402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12402
  have eq13265 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq13109
    | exact resolve eq13109 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13109
  have eq13630 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq13108
  have eq13680 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq876 eq13630
    | exact resolve eq13630 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq13630
  have eq13895 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12364 eq13680
    | exact resolve eq13680 eq12364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12364 eq13680
  have eq13910 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq13895
  have eq15049 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13910 eq97
    | exact resolve eq97 eq13910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq13910
  have eq15069 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq15049
  have eq15083 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15069
       have r₂ := eq12367
       grind)
    | exact resolve eq15069 eq12367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12367 eq15069
  have eq15195 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq872 x x
       have i₂ := eq15083
       grind)
    | exact superpose eq15083 eq872
    | exact resolve eq872 eq15083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq15083
  have eq15198 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15195
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15195
    | exact resolve eq15195 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15195
  have eq15284 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq15198
  have eq15286 : x = (M.op x y) := by
    first
    | (have r₁ := eq15284
       have r₂ := eq13265
       grind)
    | exact resolve eq15284 eq13265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13265 eq15284
  have eq15341 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq15286 eq21
    | exact resolve eq21 eq15286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq15418 : x = (M.op x x) := by
    first
    | exact superpose eq15286 eq874
    | exact resolve eq874 eq15286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq15484 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15341
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15341
    | exact resolve eq15341 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15341
  have eq15491 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15484 eq27
    | exact resolve eq27 eq15484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq15650 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq15418
       grind)
    | exact superpose eq15418 eq51
    | exact resolve eq51 eq15418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq15670 : (k x x) = (M.op x x) := by grind
  have eq15721 : x = (k x x) := by
    first
    | (have i₁ := eq15670
       have i₂ := eq15418
       grind)
    | exact superpose eq15418 eq15670
    | exact resolve eq15670 eq15418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15670
  have eq15739 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq15286 eq15650
    | exact resolve eq15650 eq15286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15650
  have eq15756 : y = (M.op x y) := by
    first
    | (have i₁ := eq15739
       have i₂ := eq15418
       grind)
    | exact superpose eq15418 eq15739
    | exact resolve eq15739 eq15418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15418 eq15739
  have eq15763 : y = (M.op x y) := by
    first
    | (have i₁ := eq15756
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15756
    | exact resolve eq15756 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq15756
  have eq15766 : x = y := by
    first
    | exact superpose eq15286 eq15763
    | exact resolve eq15763 eq15286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15286 eq15763
  have eq15769 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq15766
       grind)
    | exact superpose eq15766 eq25
    | exact resolve eq25 eq15766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15766
  have eq15906 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15769
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15769
    | exact resolve eq15769 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15769
  have eq15968 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15484 eq15906
    | exact resolve eq15906 eq15484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15906
  have eq16203 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15968 eq15491
    | exact resolve eq15491 eq15968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15491 eq15968
  have eq17819 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq706 x x
       have i₂ := eq15721
       grind)
    | exact superpose eq15721 eq706
    | (have j0 := eq706 x x
       grind)
    | exact resolve eq706 eq15721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq15721
  have eq17822 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq17819
  have eq17823 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq17822
  have eq17834 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17823
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17823
    | exact resolve eq17823 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17823
  have eq17848 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15484 eq17834
    | exact resolve eq17834 eq15484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15484 eq17834
  have eq19687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16203 eq17848
    | exact resolve eq17848 eq16203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16203 eq17848
  have eq19688 : False := by grind
  exact eq19688

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyy_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
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
  have eq28 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq37 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
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
  have eq40 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X4) X3) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq21 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) X5)) X1) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq20 X1 (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X0 X5
       have i₂ := eq21 X3 X2 X4 X0
       grind)
    | exact superpose eq21 eq20
    | exact resolve eq20 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq21
  have eq102 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36 y x
       grind)
    | exact superpose eq36 eq16
    | (have j1 := eq36 y x
       grind)
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq125 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq353 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq13
    | (have j0 := eq13 X1 (τ X0)
       have j1 := eq37 X0 X1
       grind)
    | (have r₁ := eq13 X1 (τ X0)
       have r₂ := eq37 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X0)
       have r₂ := eq37 X0 (τ X0)
       grind)
    | (have r₁ := eq13 X0 (M.op (τ X0) (τ X0))
       have r₂ := eq37 X0 (M.op (M.op (τ X0) (τ X0)) X0)
       grind)
    | exact resolve eq13 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq37 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq362 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq361 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq363 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq353 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq364 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (k X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq363 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq366 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq362 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq362
    | (have j0 := eq362 X0
       grind)
    | exact resolve eq362 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq711 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq74 X0 X1 X2 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq729 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq711 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq711
    | exact resolve eq711 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq1920 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) (M.op X0 X4)) (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq83 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X1 X0 X2 X4
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq83
    | exact resolve eq83 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1959 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op X0 X3) (M.op X0 X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1920 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq1920
    | exact resolve eq1920 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1920
  have eq3410 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq366 X0
       grind)
    | exact superpose eq366 eq10
    | (have j1 := eq366 X0
       grind)
    | exact resolve eq10 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq3841 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq3410 X0
       grind)
    | exact superpose eq3410 eq28
    | (have j1 := eq3410 X0
       grind)
    | exact resolve eq28 eq3410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq3891 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3410 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3410
  have eq3915 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3841 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3841
    | (have j0 := eq3841 X0
       grind)
    | exact resolve eq3841 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3841
  have eq4055 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq33 X0 (σ X0)
       have i₂ := eq3915 (σ X0)
       grind)
    | exact superpose eq3915 eq33
    | (have j1 := eq3915 (σ X0)
       grind)
    | exact resolve eq33 eq3915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3915
  have eq4078 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4055 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4055
    | (have j0 := eq4055 X0
       grind)
    | exact resolve eq4055 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4055
  have eq4097 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (τ (σ X0)) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4078 X0
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq4078
    | (have j0 := eq4078 X0
       grind)
    | exact resolve eq4078 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4078
  have eq4115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4097 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4097
    | (have j0 := eq4097 X0
       grind)
    | exact resolve eq4097 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4097
  have eq7193 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq364 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq364
    | exact resolve eq364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq7288 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7193 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7193
    | (have j0 := eq7193 X0 X1
       grind)
    | exact resolve eq7193 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7193
  have eq8413 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3891 (σ X0)
       have i₂ := eq33 X0 (σ X0)
       grind)
    | exact superpose eq33 eq3891
    | exact resolve eq3891 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq3891
  have eq8418 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op (τ (σ X0)) (τ (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq8413 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8413
    | (have j0 := eq8413 X0
       grind)
    | exact resolve eq8413 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8413
  have eq8421 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq8418 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8418
    | (have j0 := eq8418 X0
       grind)
    | exact resolve eq8418 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8418
  have eq8424 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8421 X0
       have j1 := eq4115 X0
       grind)
    | (have r₁ := eq8421 X0
       have r₂ := eq4115 X0
       grind)
    | exact resolve eq8421 eq4115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4115 eq8421
  have eq8636 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq8424 (σ X0)
       grind)
    | exact superpose eq8424 eq15
    | exact resolve eq15 eq8424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8644 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0 X0
       have i₂ := eq8424 (τ X0)
       grind)
    | exact superpose eq8424 eq40
    | exact resolve eq40 eq8424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq8673 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8644 X0
       have i₂ := eq8424 X0
       grind)
    | exact superpose eq8424 eq8644
    | exact resolve eq8644 eq8424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8644
  have eq8679 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8636 X0
       have i₂ := eq8424 X0
       grind)
    | exact superpose eq8424 eq8636
    | exact resolve eq8636 eq8424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8424 eq8636
  have eq9093 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq125 (τ X0) X1
       have i₂ := eq8673 X0
       grind)
    | exact superpose eq8673 eq125
    | exact resolve eq125 eq8673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9397 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq8679 X0
       grind)
    | exact superpose eq8679 eq9
    | exact resolve eq9 eq8679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9445 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq729 (σ X0) (σ X0)
       have i₂ := eq8679 X0
       grind)
    | exact superpose eq8679 eq729
    | exact resolve eq729 eq8679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13388 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (σ X0)) X1) (σ (σ (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9397 (σ X0) X1
       have i₂ := eq8679 X0
       grind)
    | exact superpose eq8679 eq9397
    | exact resolve eq9397 eq8679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9397
  have eq63721 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ X1) X0) ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq7288 (τ X0) X1
       grind)
    | exact superpose eq7288 eq19
    | (have j1 := eq7288 (τ X0) X1
       grind)
    | exact resolve eq19 eq7288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7288
  have eq63945 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63721 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63721
    | (have j0 := eq63721 X0 X1
       grind)
    | exact resolve eq63721 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63721
  have eq64013 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k (σ X1) X0) = X0 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63945 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq63945
    | (have j0 := eq63945 X0 X1
       grind)
    | exact resolve eq63945 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq63945
  have eq64055 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64013 X0 X1
       have i₂ := eq8673 X0
       grind)
    | exact superpose eq8673 eq64013
    | (have j0 := eq64013 X0 X1
       grind)
    | exact resolve eq64013 eq8673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8673 eq64013
  have eq917189 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) X0)) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64055 (σ X1) X0
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq64055
    | (have j0 := eq64055 (σ X1) X0
       grind)
    | exact resolve eq64055 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64055
  have eq917838 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq917189 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq917189
    | (have j0 := eq917189 X0 X1
       grind)
    | exact resolve eq917189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917189
  have eq918023 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq917838 X0 X1
       have i₂ := eq8679 X1
       grind)
    | exact superpose eq8679 eq917838
    | (have j0 := eq917838 X0 X1
       grind)
    | exact resolve eq917838 eq8679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917838
  have eq918152 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq918023 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq918023
    | (have j0 := eq918023 X0 X1
       grind)
    | exact resolve eq918023 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918023
  have eq920210 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq102
       have i₂ := eq918152 y x
       grind)
    | exact superpose eq918152 eq102
    | (have j1 := eq918152 y x
       grind)
    | (have r₁ := eq102
       have r₂ := eq918152 y x
       grind)
    | exact resolve eq102 eq918152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq918152
  have eq920635 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq920210
  have eq920692 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq111 x y
       grind)
    | (have r₁ := eq920635
       have r₂ := eq111 x y
       grind)
    | exact resolve eq920635 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq920635
  have eq920850 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq920692
       have i₂ := eq8679 x
       grind)
    | exact superpose eq8679 eq920692
    | exact resolve eq920692 eq8679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920692
  have eq924746 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq920850
       grind)
    | exact superpose eq920850 eq10
    | exact resolve eq10 eq920850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920850
  have eq925222 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq924746
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq924746
    | exact resolve eq924746 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924746
  have eq925223 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq925222
  have eq926947 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq729 (σ x) (σ y)
       have i₂ := eq925223
       grind)
    | exact superpose eq925223 eq729
    | exact resolve eq729 eq925223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925223
  have eq927643 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq926947
       have i₂ := eq8679 x
       grind)
    | exact superpose eq8679 eq926947
    | exact resolve eq926947 eq8679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8679 eq926947
  have eq929390 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq927643
       grind)
    | exact superpose eq927643 eq10
    | exact resolve eq10 eq927643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927643
  have eq929872 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq929390
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq929390
    | exact resolve eq929390 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929390
  have eq929978 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9445 x
       have i₂ := eq929872
       grind)
    | exact superpose eq929872 eq9445
    | exact resolve eq9445 eq929872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9445
  have eq930286 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq729 x x
       have i₂ := eq929872
       grind)
    | exact superpose eq929872 eq729
    | exact resolve eq729 eq929872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929872
  have eq955947 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq929978
       grind)
    | exact superpose eq929978 eq16
    | exact resolve eq16 eq929978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929978
  have eq960059 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq955947
       have i₂ := eq930286
       grind)
    | exact superpose eq930286 eq955947
    | exact resolve eq955947 eq930286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930286 eq955947
  have eq960061 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by grind
  clear eq960059
  have eq960062 : x = (M.op x x) := by grind
  clear eq960061
  have eq960069 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq125 x X0
       have i₂ := eq960062
       grind)
    | exact superpose eq960062 eq125
    | exact resolve eq125 eq960062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq960106 : ∀ X0 : G, (M.op (M.op (M.op (τ x) X0) (τ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9093 x X0
       have i₂ := eq960062
       grind)
    | exact superpose eq960062 eq9093
    | exact resolve eq9093 eq960062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9093
  have eq960829 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq1959 x x x
       have i₂ := eq960062
       grind)
    | exact superpose eq960062 eq1959
    | exact resolve eq1959 eq960062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960062
  have eq960914 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq960829 X0
       have i₂ := eq729 x X0
       grind)
    | (have i₁ := eq960829 X0
       have i₂ := eq729 x (M.op x X0)
       grind)
    | exact superpose eq729 eq960829
    | exact resolve eq960829 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729 eq960829
  have eq967529 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq960069 X0
       have i₂ := eq960914 X0
       grind)
    | exact superpose eq960914 eq960069
    | exact resolve eq960069 eq960914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960069 eq960914
  have eq969921 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1959 x X1 X0
       have i₂ := eq967529 X0
       grind)
    | exact superpose eq967529 eq1959
    | exact resolve eq1959 eq967529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq971560 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq969921 X0 X0
       have i₂ := eq967529 X0
       grind)
    | exact superpose eq967529 eq969921
    | exact resolve eq969921 eq967529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969921
  have eq1291926 : ∀ X0 : G, (M.op (τ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq960106 X0
       have i₂ := eq971560 X0 (τ x)
       grind)
    | exact superpose eq971560 eq960106
    | exact resolve eq960106 eq971560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960106
  have eq1294712 : ∀ X0 : G, (M.op (M.op (M.op (σ (σ (τ x))) X0) (σ (σ (τ x)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13388 (τ x) X0
       have i₂ := eq1291926 (τ x)
       grind)
    | exact superpose eq1291926 eq13388
    | exact resolve eq13388 eq1291926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13388 eq1291926
  have eq1297475 : ∀ X0 : G, (M.op (σ (σ (τ x))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1294712 X0
       have i₂ := eq971560 X0 (σ (σ (τ x)))
       grind)
    | exact superpose eq971560 eq1294712
    | exact resolve eq1294712 eq971560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971560 eq1294712
  have eq1297962 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1297475 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq1297475
    | exact resolve eq1297475 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297475
  have eq1301686 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1297962 (σ y)
       grind)
    | exact superpose eq1297962 eq16
    | exact resolve eq16 eq1297962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297962
  have eq1304679 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1301686
       have i₂ := eq967529 y
       grind)
    | exact superpose eq967529 eq1301686
    | exact resolve eq1301686 eq967529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967529 eq1301686
  have eq1304680 : False := by grind
  exact eq1304680

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_y_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq47 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq48 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq16
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92
    | exact resolve eq92 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq216 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ y)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq381 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq389 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq381 X0
       grind)
    | exact superpose eq381 eq14
    | exact resolve eq14 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq700 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq65 X0 X0
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq711 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq700 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq714 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq711 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq711 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq711 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq711 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq724 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq714 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq714
    | (have j0 := eq714 X0 X1
       grind)
    | exact resolve eq714 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq1007 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq389 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq389
    | exact resolve eq389 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1010 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq389
    | exact resolve eq389 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1012 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51 eq389
    | exact resolve eq389 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq389
  have eq10062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10063 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10062
    | exact resolve eq10062 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10062
  have eq10074 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10063
       have r₂ := eq28
       grind)
    | exact resolve eq10063 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10063
  have eq10076 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10074
    | exact resolve eq10074 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10074
  have eq10096 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  have eq10131 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq10076 eq1007
    | exact resolve eq1007 eq10076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10076
  have eq10132 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10131
    | exact resolve eq10131 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10131
  have eq10153 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10132
  have eq10374 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq708 x y
       have i₂ := eq10153
       grind)
    | exact superpose eq10153 eq708
    | (have j0 := eq708 x y
       grind)
    | exact resolve eq708 eq10153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708 eq10153
  have eq10473 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10374
  have eq10566 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10473
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10473
    | exact resolve eq10473 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10473
  have eq10658 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10566
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10566
    | exact resolve eq10566 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10566
  have eq10746 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10658
    | exact resolve eq10658 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10658
  have eq10747 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10746
  have eq10833 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10747
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10747
    | exact resolve eq10747 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10747
  have eq10919 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10833
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10833
    | exact resolve eq10833 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10833
  have eq10987 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10919 eq1007
    | exact resolve eq1007 eq10919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10919
  have eq10988 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10987
    | exact resolve eq10987 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10987
  have eq10989 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10988
  have eq10991 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10989 eq28
    | exact resolve eq28 eq10989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10989
  have eq12547 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq10096 eq97
    | exact resolve eq97 eq10096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq10096
  have eq12571 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq29 eq12547
    | exact resolve eq12547 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12547
  have eq15061 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by grind
  clear eq12571
  have eq15097 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15061
  have eq15847 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq15097
       grind)
    | exact superpose eq15097 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq15097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15097
  have eq15856 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15847
  have eq15864 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15856
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15856
    | exact resolve eq15856 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15856
  have eq15865 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15864
  have eq15967 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1007 x x
       have i₂ := eq15865
       grind)
    | exact superpose eq15865 eq1007
    | exact resolve eq1007 eq15865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15865
  have eq15970 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15967
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15967
    | exact resolve eq15967 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15967
  have eq15975 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15970 eq28
    | exact resolve eq28 eq15970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15979 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15970 eq216
    | exact resolve eq216 eq15970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16002 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15970 eq1012
    | exact resolve eq1012 eq15970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19863 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16002 eq15979
    | exact resolve eq15979 eq16002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15979 eq16002
  have eq19913 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq19863
  have eq19917 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq19913
    | exact resolve eq19913 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19913
  have eq19956 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19917 eq15970
    | exact resolve eq15970 eq19917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15970
  have eq19963 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq19956
  have eq20001 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19963 eq27
    | exact resolve eq27 eq19963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19963
  have eq20685 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20001
  have eq20769 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19917 eq20685
    | exact resolve eq20685 eq19917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19917 eq20685
  have eq20792 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20769
  have eq21205 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20792 eq100
    | exact resolve eq100 eq20792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq20792
  have eq21224 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq21205
  have eq21239 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq21224
       have r₂ := eq15975
       grind)
    | exact resolve eq21224 eq15975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15975 eq21224
  have eq21913 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1007 x x
       have i₂ := eq21239
       grind)
    | exact superpose eq21239 eq1007
    | exact resolve eq1007 eq21239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq21239
  have eq21918 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21913
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21913
    | exact resolve eq21913 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21913
  have eq21919 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq21918
  have eq21923 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21919 eq21
    | exact resolve eq21 eq21919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21919
  have eq22065 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21923
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21923
    | exact resolve eq21923 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21923
  have eq22147 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22065 eq10991
    | (have r₁ := eq10991
       have r₂ := eq22065
       grind)
    | exact resolve eq10991 eq22065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10991
  have eq22183 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22147
  have eq22184 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22183
  have eq22249 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22184 eq216
    | exact resolve eq216 eq22184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq22276 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22184 eq1012
    | exact resolve eq1012 eq22184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012 eq22184
  have eq28991 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22276 eq22249
    | exact resolve eq22249 eq22276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22249 eq22276
  have eq29049 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq28991
  have eq29060 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq29049
    | exact resolve eq29049 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29049
  have eq29068 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29060 eq28
    | exact resolve eq28 eq29060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29060
  have eq29147 : x = (M.op x y) := by
    first
    | (have r₁ := eq29068
       have r₂ := eq22065
       grind)
    | exact resolve eq29068 eq22065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22065 eq29068
  have eq29151 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq29147 eq21
    | exact resolve eq21 eq29147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq29232 : x = (M.op x x) := by
    first
    | exact superpose eq29147 eq1010
    | exact resolve eq1010 eq29147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq29301 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq29151
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29151
    | exact resolve eq29151 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29151
  have eq29313 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq29301 eq27
    | exact resolve eq27 eq29301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq29500 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq29232
       grind)
    | exact superpose eq29232 eq47
    | exact resolve eq47 eq29232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq29524 : x = (k x x) := by grind
  have eq29614 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq29147 eq29500
    | exact resolve eq29500 eq29147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29500
  have eq29643 : y = (M.op x y) := by
    first
    | (have i₁ := eq29614
       have i₂ := eq29232
       grind)
    | exact superpose eq29232 eq29614
    | exact resolve eq29614 eq29232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29232 eq29614
  have eq29660 : y = (M.op x y) := by
    first
    | (have i₁ := eq29643
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29643
    | exact resolve eq29643 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq29643
  have eq29667 : x = y := by
    first
    | exact superpose eq29147 eq29660
    | exact resolve eq29660 eq29147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29147 eq29660
  have eq29681 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq29667
       grind)
    | exact superpose eq29667 eq25
    | exact resolve eq25 eq29667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq29667
  have eq29833 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq29681
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29681
    | exact resolve eq29681 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29681
  have eq29897 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29301 eq29833
    | exact resolve eq29833 eq29301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29833
  have eq30462 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq29897 eq29313
    | exact resolve eq29313 eq29897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29313 eq29897
  have eq30547 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq724 x x
       have i₂ := eq29524
       grind)
    | exact superpose eq29524 eq724
    | (have j0 := eq724 x x
       grind)
    | exact resolve eq724 eq29524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq29524
  have eq30552 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq30547
  have eq30553 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq30552
  have eq30570 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq30553
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30553
    | exact resolve eq30553 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq30553
  have eq30589 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq29301 eq30570
    | exact resolve eq30570 eq29301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29301 eq30570
  have eq30700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30462 eq30589
    | exact resolve eq30589 eq30462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30462 eq30589
  have eq30701 : False := by grind
  exact eq30701

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_y_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq25 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq31 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
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
  have eq54 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq31 (τ X0)
       grind)
    | exact superpose eq31 eq19
    | exact resolve eq19 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq54 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54
    | exact resolve eq54 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq76 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq77 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X2 X1) (M.op X2 X0)) X3) X1) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X2 X1) (M.op X2 X0)) X1
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq106 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X2) = X2 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op X1 X2) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (k X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq120 : ∀ X0 X1 : G, (k (σ (τ X1)) X1) = X1 ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq126 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq120 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq120
    | (have j0 := eq120 X0 X1
       grind)
    | exact resolve eq120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq145 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq76 X1 x x X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1 X0 (M.op X1 X0)
       have i₂ := eq145 (M.op X1 X0)
       grind)
    | exact superpose eq145 eq76
    | exact resolve eq76 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq9
    | exact resolve eq9 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq174 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq155 X1 (M.op X1 X0)
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq155
    | exact resolve eq155 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq194 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X1 X2) (M.op X1 X0)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X2) X1 X0
       have i₂ := eq174 X2 X1
       grind)
    | exact superpose eq174 eq9
    | exact resolve eq9 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X3 X0) (M.op X3 X2)) X1)) X5) X0) X4) X5) X4) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq77 X0 X5 (M.op X0 (M.op (M.op (M.op X3 X0) (M.op X3 X2)) X1)) X4
       have i₂ := eq76 X0 X3 X2 X1
       grind)
    | exact superpose eq76 eq77
    | exact resolve eq77 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq77
  have eq321 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq126 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq322 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq321 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq321
    | (have j0 := eq321 (σ X0)
       grind)
    | exact resolve eq321 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq361 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  clear eq105
  have eq1055 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq361 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq1057 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1055 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1072 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X1 ∨ (k X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1057 X1
       have i₂ := eq114 X0 X1
       grind)
    | (have i₁ := eq1057 X0
       have i₂ := eq114 (M.op X0 X0) X1
       grind)
    | exact superpose eq114 eq1057
    | (have j0 := eq1057 X1
       have j1 := eq114 X0 X1
       grind)
    | (have r₁ := eq1057 X0
       have r₂ := eq114 X0 X0
       grind)
    | (have r₁ := eq1057 (M.op X1 X1)
       have r₂ := eq114 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq1057 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1078 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1072 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1078 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1108 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1106 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq1106
    | exact resolve eq1106 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq2778 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) X2) X3) = X3 ∨ (M.op (M.op (M.op X2 X0) X1) X0) = X0 ∨ (M.op X2 X1) = (k X1 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X2 X2
       have i₂ := eq106 X1 X2 X0
       grind)
    | exact superpose eq106 eq9
    | (have j1 := eq106 X1 X2 X0
       grind)
    | exact resolve eq9 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq2967 : ∀ X0 : G, (k (σ (σ (τ (k (τ X0) (τ X0))))) X0) = X0 ∨ (τ (τ X0)) = (τ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq1108 (τ X0)
       grind)
    | exact superpose eq1108 eq55
    | (have j1 := eq1108 (τ X0)
       grind)
    | exact resolve eq55 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq3019 : ∀ X0 : G, (k (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (τ (τ X0)) = (τ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2967 X0
       have i₂ := eq11 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq11 eq2967
    | (have j0 := eq2967 X0
       grind)
    | exact resolve eq2967 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2967
  have eq3026 : ∀ X0 : G, (k (k (σ (τ X0)) X0) X0) = X0 ∨ (τ (τ X0)) = (τ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3019 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq3019
    | (have j0 := eq3019 X0
       grind)
    | exact resolve eq3019 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3019
  have eq3032 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (τ (τ X0)) = (τ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3026 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3026
    | (have j0 := eq3026 X0
       grind)
    | exact resolve eq3026 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3026
  have eq3037 : ∀ X0 : G, (τ (τ X0)) = (τ (τ (k X0 X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3032 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq3032
    | (have j0 := eq3032 X0
       grind)
    | exact resolve eq3032 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3032
  have eq3085 : ∀ X0 X1 : G, (k (τ (τ X0)) (τ X1)) = (τ (k (τ (k X0 X0)) X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ (k X0 X0))
       have i₂ := eq3037 X0
       grind)
    | exact superpose eq3037 eq32
    | (have j1 := eq3037 X0
       grind)
    | exact resolve eq32 eq3037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3112 : ∀ X0 X1 : G, (τ (k (τ X0) X1)) = (τ (k (τ (k X0 X0)) X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3085 X0 X1
       have i₂ := eq32 X1 (τ X0)
       grind)
    | exact superpose eq32 eq3085
    | (have j0 := eq3085 X0 X1
       grind)
    | exact resolve eq3085 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3085
  have eq3677 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq322 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq3710 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3677 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq3677
    | (have j0 := eq3677 (τ X0)
       grind)
    | exact resolve eq3677 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3677
  have eq3719 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3710 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq3710
    | (have j0 := eq3710 X0
       grind)
    | exact resolve eq3710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3710
  have eq3720 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3719 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3719
    | (have j0 := eq3719 X0
       grind)
    | exact resolve eq3719 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3719
  have eq3721 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3720 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3720
    | (have j0 := eq3720 X0
       grind)
    | exact resolve eq3720 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3720
  have eq3738 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3721 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq3721
    | (have j0 := eq3721 (τ X0)
       grind)
    | exact resolve eq3721 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3721
  have eq4089 : ∀ X0 X1 : G, (τ X1) ≠ (τ X1) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3738 X1
       have i₂ := eq114 X0 X1
       grind)
    | exact superpose eq114 eq3738
    | (have j0 := eq3738 X1
       have j1 := eq114 X0 X1
       grind)
    | exact resolve eq3738 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq3738
  have eq4095 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq4089 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4089
  have eq25104 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq125 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq125
    | (have j0 := eq125 X0 X1
       grind)
    | exact resolve eq125 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq25745 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25104 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq25104
    | (have j0 := eq25104 X0 X1
       grind)
    | exact resolve eq25104 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25104
  have eq300791 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X1)) ∨ (τ X1) = (τ (k X1 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1108 X1
       have i₂ := eq4095 X0 X1
       grind)
    | exact superpose eq4095 eq1108
    | (have j0 := eq1108 X1
       have j1 := eq4095 X0 X1
       grind)
    | exact resolve eq1108 eq4095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108 eq4095
  have eq301878 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq300791 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300791
  have eq331316 : ∀ X0 X1 : G, (k (τ (k X0 X0)) X1) = (σ (τ (k (τ X0) X1))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (τ (k X0 X0)) X1)
       have i₂ := eq3112 X0 X1
       grind)
    | exact superpose eq3112 eq11
    | (have j1 := eq3112 X0 X1
       grind)
    | exact resolve eq11 eq3112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3112
  have eq331710 : ∀ X0 X1 : G, (k (τ X0) X1) = (k (τ (k X0 X0)) X1) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq331316 X0 X1
       have i₂ := eq11 (k (τ X0) X1)
       grind)
    | exact superpose eq11 eq331316
    | (have j0 := eq331316 X0 X1
       grind)
    | exact resolve eq331316 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331316
  have eq332156 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k (k X0 X0) (σ X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 (k X0 X0) X1
       have i₂ := eq331710 X0 X1
       grind)
    | exact superpose eq331710 eq18
    | (have j1 := eq331710 X0 X1
       grind)
    | exact resolve eq18 eq331710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331710
  have eq332490 : ∀ X0 X1 : G, (k X0 (σ X1)) = (k (k X0 X0) (σ X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq332156 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq332156
    | (have j0 := eq332156 X0 X1
       grind)
    | exact resolve eq332156 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq332156
  have eq332630 : ∀ X0 X1 : G, (k X1 X0) = (k (k X1 X1) X0) ∨ (k (k X1 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq332490 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq332490
    | (have j0 := eq332490 X1 X1
       grind)
    | exact resolve eq332490 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332490
  have eq334754 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq332630 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332630
  have eq334888 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (k (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq334754 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq334754
    | exact resolve eq334754 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334754
  have eq334930 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq334888 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq334888
    | (have j0 := eq334888 X0
       grind)
    | exact resolve eq334888 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334888
  have eq335141 : ∀ X0 : G, (τ (τ X0)) ≠ (τ (τ (k X0 X0))) ∨ (τ (τ X0)) = (τ (k (τ (k X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq334930 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq334930
    | exact resolve eq334930 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334930
  have eq335214 : ∀ X0 : G, (τ (τ X0)) ≠ (τ (τ (k X0 X0))) ∨ (τ (τ X0)) = (τ (τ (k (k X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq335141 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq335141
    | (have j0 := eq335141 X0
       grind)
    | exact resolve eq335141 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335141
  have eq540788 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (M.op (M.op (M.op X0 X1) X0) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2778 X1 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2778
  have eq540789 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq540788 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540788
  have eq541351 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X1 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq540789 X0 (M.op X1 X0)
       have i₂ := eq152 X0 X1
       grind)
    | exact superpose eq152 eq540789
    | (have j0 := eq540789 X0 X1
       grind)
    | exact resolve eq540789 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542292 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq152 X0 X1
       have i₂ := eq541351 X0 X1
       grind)
    | exact superpose eq541351 eq152
    | (have j1 := eq541351 X0 X1
       grind)
    | exact resolve eq152 eq541351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq541351
  have eq543319 : ∀ X0 X4 : G, (M.op (M.op X0 X4) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X4
    first
    | (have i₁ := eq290 X0 x x x X0 X4
       have i₂ := eq542292 X0 (M.op (M.op X0 (M.op (M.op (M.op x X0) (M.op x x)) x)) X4)
       grind)
    | exact superpose eq542292 eq290
    | (have j1 := eq542292 X0 x
       grind)
    | exact resolve eq290 eq542292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq542292
  have eq544018 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = (k X1 X1) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq540789 X1 X0
       have i₂ := eq543319 X1 X0
       grind)
    | exact superpose eq543319 eq540789
    | (have j0 := eq540789 X1 X1
       have j1 := eq543319 X1 x
       grind)
    | exact resolve eq540789 eq543319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540789 eq543319
  have eq544355 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq544018 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544018
  have eq544480 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq544355 X1 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq544355
    | (have j0 := eq544355 X1 (σ X0)
       grind)
    | exact resolve eq544355 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544355
  have eq549613 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq174 (σ X0) (σ X0)
       have i₂ := eq544480 X0 X1
       grind)
    | exact superpose eq544480 eq174
    | (have j1 := eq544480 X0 (σ (k X0 X0))
       grind)
    | exact resolve eq174 eq544480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544480
  have eq639598 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq549613 X0 (σ (k X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549613
  have eq639599 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq639598 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639598
  have eq640082 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (k X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ (k X0 X0))
       have i₂ := eq639599 X0
       grind)
    | exact superpose eq639599 eq9
    | exact resolve eq9 eq639599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1484262 : ∀ X0 : G, (τ (τ X0)) ≠ (τ (τ X0)) ∨ (τ (τ X0)) = (τ (τ (k (k X0 X0) X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq335214 X0
       have i₂ := eq3037 X0
       grind)
    | exact superpose eq3037 eq335214
    | (have j0 := eq335214 X0
       have j1 := eq3037 X0
       grind)
    | (have r₁ := eq335214 X0
       have r₂ := eq3037 X0
       grind)
    | exact resolve eq335214 eq3037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3037 eq335214
  have eq1484282 : ∀ X0 : G, (τ (τ X0)) = (τ (τ (k (k X0 X0) X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1484262 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484262
  have eq1484794 : ∀ X0 : G, (τ (k (k X0 X0) X0)) = (σ (τ (τ X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (τ (k (k X0 X0) X0))
       have i₂ := eq1484282 X0
       grind)
    | exact superpose eq1484282 eq11
    | (have j1 := eq1484282 X0
       grind)
    | exact resolve eq11 eq1484282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484282
  have eq1485079 : ∀ X0 : G, (τ X0) = (τ (k (k X0 X0) X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1484794 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq1484794
    | (have j0 := eq1484794 X0
       grind)
    | exact resolve eq1484794 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484794
  have eq1485503 : ∀ X0 : G, (σ (τ X0)) = (k (k X0 X0) X0) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k (k X0 X0) X0)
       have i₂ := eq1485079 X0
       grind)
    | exact superpose eq1485079 eq11
    | (have j1 := eq1485079 X0
       grind)
    | exact resolve eq11 eq1485079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485079
  have eq1485932 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1485503 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1485503
    | (have j0 := eq1485503 X0
       grind)
    | exact resolve eq1485503 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485503
  have eq1485933 : ∀ X0 : G, (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1485932 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485932
  have eq1704262 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X1 X1) = X1 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1
       have i₂ := eq130 X0 X1
       grind)
    | (have i₁ := eq31 X0
       have i₂ := eq130 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq130 eq31
    | (have j1 := eq130 X0 X1
       grind)
    | exact resolve eq31 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq1705498 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (τ (σ X0)) X0) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq1704262 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704262
  have eq1705499 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (τ (σ X0)) X0) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq1705498 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705498
  have eq1705635 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (τ (σ X0)) X0) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1705499 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1705499
    | (have j0 := eq1705499 X0
       grind)
    | exact resolve eq1705499 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705499
  have eq1705693 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1705635 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1705635
    | (have j0 := eq1705635 X0
       grind)
    | exact resolve eq1705635 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705635
  have eq1705770 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq639599 X0
       have i₂ := eq1705693 X0
       grind)
    | exact superpose eq1705693 eq639599
    | (have j1 := eq1705693 X0
       grind)
    | exact resolve eq639599 eq1705693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705693
  have eq1709724 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq1705770 X0
       grind)
    | exact superpose eq1705770 eq13
    | (have j0 := eq13 (k X0 X0) X0
       have j1 := eq1705770 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq1705770 X0
       grind)
    | exact resolve eq13 eq1705770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705770
  have eq1710009 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1709724 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1709724
  have eq1713259 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X1 (σ (τ X0))) = X1 ∨ (σ (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1710009 (τ X0) X1
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq1710009
    | (have j0 := eq1710009 (τ X0) X1
       grind)
    | exact resolve eq1710009 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1710009
  have eq1713780 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (σ (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1713259 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1713259
    | (have j0 := eq1713259 X0 X1
       grind)
    | exact resolve eq1713259 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713259
  have eq1713797 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1713780 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1713780
    | (have j0 := eq1713780 X0 X1
       grind)
    | exact resolve eq1713780 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713780
  have eq1732478 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = X0 ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1713797 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq1713797
    | (have j0 := eq1713797 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | exact resolve eq1713797 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1713797
  have eq1733280 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = X0 ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1732478 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732478
  have eq1738324 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1733280 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1733280
    | exact resolve eq1733280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1733280
  have eq1738757 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1738324 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq1738324
    | (have j0 := eq1738324 X0
       grind)
    | exact resolve eq1738324 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738324
  have eq1738767 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1738757 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1738757
    | (have j0 := eq1738757 X0
       grind)
    | exact resolve eq1738757 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738757
  have eq1738976 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (k (τ X0) (M.op X1 X1)) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 (M.op X1 X1)
       have i₂ := eq1738767 X1
       grind)
    | exact superpose eq1738767 eq23
    | (have j1 := eq1738767 X1
       grind)
    | exact resolve eq23 eq1738767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738767
  have eq1739235 : ∀ X0 X1 : G, (k (τ X0) X1) = (k (τ X0) (M.op X1 X1)) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1738976 X0 X1
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq1738976
    | (have j0 := eq1738976 X0 X1
       grind)
    | exact resolve eq1738976 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1738976
  have eq1748980 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1739235 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1739235
    | (have j0 := eq1739235 X0 X1
       grind)
    | exact resolve eq1739235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739235
  have eq1749941 : ∀ X0 : G, (M.op X0 X0) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1485933 (M.op X0 X0)
       have i₂ := eq1748980 (M.op X0 X0) X0
       grind)
    | exact superpose eq1748980 eq1485933
    | (have j1 := eq1748980 X0 X0
       grind)
    | exact resolve eq1485933 eq1748980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485933
  have eq1750278 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq1749941
  have eq1750742 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1748980 X0 X0
       have i₂ := eq1750278 X0
       grind)
    | exact superpose eq1750278 eq1748980
    | (have j0 := eq1748980 X0 X0
       have j1 := eq1750278 X0
       grind)
    | exact resolve eq1748980 eq1750278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748980 eq1750278
  have eq1750818 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1750742 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750742
  have eq1751119 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1750818 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1750818
    | exact resolve eq1750818 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1751157 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq301878 X1 X0
       have i₂ := eq1750818 X0
       grind)
    | exact superpose eq1750818 eq301878
    | (have j0 := eq301878 X1 X0
       grind)
    | exact resolve eq301878 eq1750818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301878
  have eq1751225 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq639599 X0
       have i₂ := eq1750818 X0
       grind)
    | exact superpose eq1750818 eq639599
    | exact resolve eq639599 eq1750818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639599
  have eq1751228 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq640082 X0 X1
       have i₂ := eq1750818 X0
       grind)
    | exact superpose eq1750818 eq640082
    | exact resolve eq640082 eq1750818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640082
  have eq1751355 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1751119 X0
       have i₂ := eq1750818 X0
       grind)
    | exact superpose eq1750818 eq1751119
    | exact resolve eq1751119 eq1750818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750818 eq1751119
  have eq1793280 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1751157 (σ X0) X1
       have i₂ := eq1751355 X0
       grind)
    | exact superpose eq1751355 eq1751157
    | (have j0 := eq1751157 (σ X0) X1
       grind)
    | exact resolve eq1751157 eq1751355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751157 eq1751355
  have eq1794246 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1793280 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1793280
    | (have j0 := eq1793280 X0 X1
       grind)
    | exact resolve eq1793280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793280
  have eq1794265 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1794246 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1794246
    | (have j0 := eq1794246 X0 X1
       grind)
    | exact resolve eq1794246 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794246
  have eq1848598 : ∀ X0 X1 : G, (M.op X0 X0) = (τ X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq1794265 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1794265 X0 (σ X0)
       grind)
    | exact superpose eq1794265 eq10
    | (have j1 := eq1794265 X0 X1
       grind)
    | exact resolve eq10 eq1794265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794265
  have eq1850973 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1848598 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1848598
    | (have j0 := eq1848598 X1 (σ X0)
       grind)
    | exact resolve eq1848598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848598
  have eq1852967 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1850973 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1850973
    | (have j0 := eq1850973 X0 X1
       grind)
    | exact resolve eq1850973 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850973
  have eq1859886 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1852967 y x
       grind)
    | exact superpose eq1852967 eq16
    | (have j1 := eq1852967 y x
       grind)
    | exact resolve eq16 eq1852967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852967
  have eq1861801 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1859886
       have i₂ := eq25745 y x
       grind)
    | exact superpose eq25745 eq1859886
    | (have j1 := eq25745 y x
       grind)
    | (have r₁ := eq1859886
       have r₂ := eq25745 y x
       grind)
    | exact resolve eq1859886 eq25745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25745 eq1859886
  have eq1861813 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq1861801
  have eq1861814 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq1861813
  have eq1861964 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1751225 x
       have i₂ := eq1861814
       grind)
    | exact superpose eq1861814 eq1751225
    | exact resolve eq1751225 eq1861814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751225
  have eq1862052 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq174 x x
       have i₂ := eq1861814
       grind)
    | exact superpose eq1861814 eq174
    | exact resolve eq174 eq1861814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861814
  have eq1876812 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1861964
       grind)
    | exact superpose eq1861964 eq16
    | exact resolve eq16 eq1861964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861964
  have eq1877134 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1876812
       have i₂ := eq1862052
       grind)
    | exact superpose eq1862052 eq1876812
    | exact resolve eq1876812 eq1862052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862052 eq1876812
  have eq1877139 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by grind
  clear eq1877134
  have eq1877140 : x = (M.op x x) := by grind
  clear eq1877139
  have eq1877242 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1751228 x X0
       have i₂ := eq1877140
       grind)
    | exact superpose eq1877140 eq1751228
    | exact resolve eq1751228 eq1877140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751228
  have eq1877303 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq1877140
       grind)
    | exact superpose eq1877140 eq9
    | exact resolve eq9 eq1877140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1877323 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq194 X0 x x
       have i₂ := eq1877140
       grind)
    | exact superpose eq1877140 eq194
    | exact resolve eq194 eq1877140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877140
  have eq1877472 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq1877323 X0
       have i₂ := eq174 X0 x
       grind)
    | exact superpose eq174 eq1877323
    | exact resolve eq1877323 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq1877323
  have eq1878034 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1877303 X0
       have i₂ := eq1877472 X0
       grind)
    | exact superpose eq1877472 eq1877303
    | exact resolve eq1877303 eq1877472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877303 eq1877472
  have eq1878064 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op x X0) X1) (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq194 X1 x X0
       have i₂ := eq1878034 X1
       grind)
    | exact superpose eq1878034 eq194
    | exact resolve eq194 eq1878034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq1878271 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1878064 X0 X1
       have i₂ := eq1878034 X0
       grind)
    | exact superpose eq1878034 eq1878064
    | exact resolve eq1878064 eq1878034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878064
  have eq1881278 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1877242 X0
       have i₂ := eq1878271 (σ x) X0
       grind)
    | exact superpose eq1878271 eq1877242
    | exact resolve eq1877242 eq1878271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877242 eq1878271
  have eq1881285 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1881278 (σ y)
       grind)
    | exact superpose eq1881278 eq16
    | exact resolve eq16 eq1881278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1881278
  have eq1881428 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1881285
       have i₂ := eq1878034 y
       grind)
    | exact superpose eq1878034 eq1881285
    | exact resolve eq1881285 eq1878034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878034 eq1881285
  have eq1881429 : False := by grind
  exact eq1881429

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq47 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq49 (τ X0)
       grind)
    | exact superpose eq49 eq19
    | exact resolve eq19 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq88 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq88
    | exact resolve eq88 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq88
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96
    | exact resolve eq96 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq116 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq164 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq100 X1
       grind)
    | exact superpose eq100 eq62
    | (have j0 := eq62 X0 X1
       grind)
    | exact resolve eq62 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq191 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq164 x y
       grind)
    | exact superpose eq164 eq16
    | (have j1 := eq164 x y
       grind)
    | exact resolve eq16 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq209 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq116 (σ X0)
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq116
    | exact resolve eq116 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq191
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq191
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq191
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq191
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq191 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq722 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq721
  have eq6502 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq722
       grind)
    | exact superpose eq722 eq16
    | exact resolve eq16 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq6503 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq6502
       have r₂ := eq100 x
       grind)
    | exact resolve eq6502 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6502
  have eq9404 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6503
       grind)
    | exact superpose eq6503 eq10
    | exact resolve eq10 eq6503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6503
  have eq9476 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9404
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9404
    | exact resolve eq9404 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9404
  have eq9666 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9476
       grind)
    | exact superpose eq9476 eq16
    | exact resolve eq16 eq9476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9476
  have eq9667 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq9666
       have r₂ := eq100 x
       grind)
    | exact resolve eq9666 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq9666
  have eq9911 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq9667
       grind)
    | exact superpose eq9667 eq10
    | exact resolve eq10 eq9667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9667
  have eq9983 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9911
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9911
    | exact resolve eq9911 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9911
  have eq9984 : x = (M.op y y) := by grind
  clear eq9983
  have eq10216 : y = (M.op x y) := by
    first
    | (have i₁ := eq116 y
       have i₂ := eq9984
       grind)
    | exact superpose eq9984 eq116
    | exact resolve eq116 eq9984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq10225 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq209 y
       have i₂ := eq9984
       grind)
    | exact superpose eq9984 eq209
    | exact resolve eq209 eq9984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq9984
  have eq11162 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10225
       grind)
    | exact superpose eq10225 eq16
    | exact resolve eq16 eq10225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10225
  have eq11237 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq11162
       have i₂ := eq10216
       grind)
    | exact superpose eq10216 eq11162
    | exact resolve eq11162 eq10216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10216 eq11162
  have eq11238 : False := by grind
  exact eq11238

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq47 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq49 (τ X0)
       grind)
    | exact superpose eq49 eq19
    | exact resolve eq19 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq88 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq88
    | exact resolve eq88 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq88
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96
    | exact resolve eq96 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq157 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq9
    | exact resolve eq9 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq100 X1
       grind)
    | exact superpose eq100 eq62
    | (have j0 := eq62 X0 X1
       grind)
    | exact resolve eq62 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq191 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq164 y x
       grind)
    | exact superpose eq164 eq16
    | (have j1 := eq164 y x
       grind)
    | exact resolve eq16 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq209 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq116 (σ X0)
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq116
    | exact resolve eq116 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq264 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq209 X0
       grind)
    | exact superpose eq209 eq9
    | exact resolve eq9 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq592 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op (τ X0) (τ X0))) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq264 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq264
    | exact resolve eq264 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq606 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 X1
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq592
    | exact resolve eq592 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq592
  have eq619 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq606 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq606
    | exact resolve eq606 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq606 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq157 X0 (σ X0)
       grind)
    | exact superpose eq157 eq606
    | exact resolve eq606 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq606
  have eq735 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq191
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq191
    | (have j1 := eq14 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq191
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq191
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq191 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq736 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq735
  have eq6552 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq736
       grind)
    | exact superpose eq736 eq16
    | exact resolve eq16 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq6553 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq6552
       have r₂ := eq100 x
       grind)
    | exact resolve eq6552 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6552
  have eq9769 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6553
       grind)
    | exact superpose eq6553 eq10
    | exact resolve eq10 eq6553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6553
  have eq9841 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9769
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9769
    | exact resolve eq9769 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9769
  have eq10028 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9841
       grind)
    | exact superpose eq9841 eq16
    | exact resolve eq16 eq9841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9841
  have eq10029 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10028
       have r₂ := eq100 x
       grind)
    | exact resolve eq10028 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq10028
  have eq10166 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq10029
       grind)
    | exact superpose eq10029 eq10
    | exact resolve eq10 eq10029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10029
  have eq10238 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10166
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq10166
    | exact resolve eq10166 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10166
  have eq10239 : y = (M.op x x) := by grind
  clear eq10238
  have eq10394 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq620 x
       have i₂ := eq10239
       grind)
    | exact superpose eq10239 eq620
    | exact resolve eq620 eq10239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq10436 : y = (M.op x y) := by
    first
    | (have i₁ := eq619 x x
       have i₂ := eq10239
       grind)
    | exact superpose eq10239 eq619
    | exact resolve eq619 eq10239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq10239
  have eq11655 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10394
       grind)
    | exact superpose eq10394 eq16
    | exact resolve eq16 eq10394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10394
  have eq11744 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq11655
       have i₂ := eq10436
       grind)
    | exact superpose eq10436 eq11655
    | exact resolve eq11655 eq10436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10436 eq11655
  have eq11745 : False := by grind
  exact eq11745

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq67 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq51
    | exact resolve eq51 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq67 (M.op X0 X1)
       grind)
    | exact superpose eq67 eq51
    | exact resolve eq51 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 (M.op X0 X0) X0 X2
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq51
    | exact resolve eq51 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq73 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op X1 X0)) X2
       have i₂ := eq70 X1 X0
       grind)
    | exact superpose eq70 eq9
    | exact resolve eq9 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq187 x y
       grind)
    | exact superpose eq187 eq16
    | (have j1 := eq187 x x
       grind)
    | exact resolve eq16 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq187 X0 X1
       grind)
    | exact superpose eq187 eq9
    | (have j1 := eq187 X0 X0
       grind)
    | exact resolve eq9 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0)
       have i₂ := eq187 X0 X0
       grind)
    | exact superpose eq187 eq67
    | (have j1 := eq187 X0 X0
       grind)
    | exact resolve eq67 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq365 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq187 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq366 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq365 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq369 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq362 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq385 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq366 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq366
    | (have j0 := eq366 (τ X0)
       grind)
    | exact resolve eq366 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq366
  have eq395 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq385 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq385
    | (have j0 := eq385 X0
       grind)
    | exact resolve eq385 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq402 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq395 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq395
    | (have j0 := eq395 X0
       grind)
    | exact resolve eq395 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq407 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq402 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq402
    | (have j0 := eq402 (τ X0)
       grind)
    | exact resolve eq402 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq626 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq71
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1559 : ∀ X0 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq369 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq369
    | exact resolve eq369 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq1601 : ∀ X0 : G, (M.op (k X0 (σ (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1559 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1559
    | (have j0 := eq1559 X0
       grind)
    | exact resolve eq1559 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1559
  have eq1611 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1601 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1601
    | (have j0 := eq1601 X0
       grind)
    | exact resolve eq1601 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq5588 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq347
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq347
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq347 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq5591 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq5588
  have eq6114 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq348 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq348
    | (have j0 := eq348 (τ X0) (τ X0) X2
       grind)
    | exact resolve eq348 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq348
  have eq6224 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) X2)) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6114 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6114
    | (have j0 := eq6114 X0 X0 X2
       grind)
    | exact resolve eq6114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6114
  have eq6231 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ (k X0 X1))) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6224 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6224
    | (have j0 := eq6224 X0 X0 X2
       grind)
    | exact resolve eq6224 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6224
  have eq6232 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6231 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6231
    | (have j0 := eq6231 X0 X0 X2
       grind)
    | exact resolve eq6231 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6231
  have eq6233 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6232 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6232
    | (have j0 := eq6232 X0 X1 X2
       grind)
    | exact resolve eq6232 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6232
  have eq6234 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X0 X2)) X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6233 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6233
    | (have j0 := eq6233 X0 X1 X2
       grind)
    | exact resolve eq6233 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6233
  have eq12018 : ∀ X0 X1 : G, (k X1 X0) = (M.op (M.op (k X1 X0) X0) (k X1 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83 (k X1 X0) X1 X0
       have i₂ := eq6234 X1 X0 (k X1 X0)
       grind)
    | exact superpose eq6234 eq83
    | (have j1 := eq6234 X1 X1 x
       grind)
    | exact resolve eq83 eq6234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq6234
  have eq17737 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq5591
       grind)
    | exact superpose eq5591 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq5591
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq5591
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq5591
       grind)
    | exact resolve eq12 eq5591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17853 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq17737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17737
  have eq26298 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12018 X0 X0
       have i₂ := eq1611 X0
       grind)
    | exact superpose eq1611 eq12018
    | (have j0 := eq12018 X0 X0
       have j1 := eq1611 X0
       grind)
    | exact resolve eq12018 eq1611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611 eq12018
  have eq26432 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq26298 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26298
  have eq26435 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq26432 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq26432
    | (have j0 := eq26432 (σ X0)
       grind)
    | exact resolve eq26432 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26432
  have eq201898 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ (M.op X1 X1) = (k X1 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq17853 X1
       grind)
    | exact superpose eq17853 eq12
    | (have j0 := eq12 X0 (σ x)
       have j1 := eq17853 X1
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq17853 X0
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq17853 X0
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq17853 X0
       grind)
    | exact resolve eq12 eq17853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202178 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have j0 := eq201898 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201898
  have eq208289 : ∀ X0 : G, (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq407 (σ y)
       have i₂ := eq202178 X0 (σ y)
       grind)
    | exact superpose eq202178 eq407
    | (have j0 := eq407 (σ y)
       have j1 := eq202178 X0 x
       grind)
    | exact resolve eq407 eq202178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202178
  have eq208689 : ∀ X0 : G, y ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq208289 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq208289
    | (have j0 := eq208289 X0
       grind)
    | exact resolve eq208289 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208289
  have eq208800 : ∀ X0 : G, y = (M.op y y) ∨ y ≠ (τ (M.op (σ y) (σ y))) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq208689 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq208689
    | (have j0 := eq208689 X0
       grind)
    | exact resolve eq208689 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208689
  have eq208801 : ∀ X0 : G, y ≠ (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq208800 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208800
  have eq212092 : ∀ X0 : G, y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq208801 X0
       have i₂ := eq5591
       grind)
    | exact superpose eq5591 eq208801
    | (have j0 := eq208801 X0
       grind)
    | exact resolve eq208801 eq5591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208801
  have eq212101 : ∀ X0 : G, y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq212092 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212092
  have eq212105 : ∀ X0 : G, y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq212101 X0
       have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq212101 X0
       have r₂ := eq12 X0 y
       grind)
    | (have r₁ := eq212101 X0
       have r₂ := eq12 X0 x
       grind)
    | (have r₁ := eq212101 X0
       have r₂ := eq12 X0 (σ x)
       grind)
    | exact resolve eq212101 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212101
  have eq212106 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq212105 X0
       grind)
    | (have r₁ := eq212105 X0
       have r₂ := eq10 y
       grind)
    | exact resolve eq212105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212105
  have eq214745 : (τ (M.op (σ x) (σ x))) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq407 (σ x)
       have i₂ := eq212106 (σ x)
       grind)
    | exact superpose eq212106 eq407
    | (have j0 := eq407 (σ x)
       grind)
    | exact resolve eq407 eq212106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212106
  have eq215153 : x ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq214745
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq214745
    | exact resolve eq214745 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214745
  have eq215265 : x = (M.op x x) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq215153
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq215153
    | exact resolve eq215153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215153
  have eq215266 : x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq215265
  have eq215705 : ∀ X0 : G, x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq215266
       have i₂ := eq17853 X0
       grind)
    | exact superpose eq17853 eq215266
    | (have j1 := eq17853 X0
       grind)
    | exact resolve eq215266 eq17853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17853
  have eq215714 : ∀ X0 : G, x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq215705 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215705
  have eq215718 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq215714 X0
       grind)
    | (have r₁ := eq215714 X0
       have r₂ := eq10 x
       grind)
    | exact resolve eq215714 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215714
  have eq217064 : (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq407 (σ y)
       have i₂ := eq215718 (σ y)
       grind)
    | exact superpose eq215718 eq407
    | (have j0 := eq407 (σ y)
       grind)
    | exact resolve eq407 eq215718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407 eq215718
  have eq217473 : y ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq217064
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq217064
    | exact resolve eq217064 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217064
  have eq217585 : y = (M.op y y) ∨ y ≠ (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq217473
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq217473
    | exact resolve eq217473 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217473
  have eq217586 : y ≠ (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq217585
  have eq218027 : y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq217586
       have i₂ := eq5591
       grind)
    | exact superpose eq5591 eq217586
    | exact resolve eq217586 eq5591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5591 eq217586
  have eq218036 : y ≠ (τ (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq218027
  have eq218040 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq218036
       have r₂ := eq10 y
       grind)
    | exact resolve eq218036 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218036
  have eq219545 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq215266
       have i₂ := eq218040
       grind)
    | exact superpose eq218040 eq215266
    | exact resolve eq215266 eq218040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215266 eq218040
  have eq219837 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq219545
  have eq219947 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq219837
       have r₂ := eq10 x
       grind)
    | exact resolve eq219837 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219837
  have eq219961 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq219947
       grind)
    | exact superpose eq219947 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq219947
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq219947
       grind)
    | exact resolve eq12 eq219947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219962 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq219947
       grind)
    | exact superpose eq219947 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq219947
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq219947
       grind)
    | exact resolve eq13 eq219947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219966 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq73 y X0
       have i₂ := eq219947
       grind)
    | exact superpose eq219947 eq73
    | exact resolve eq73 eq219947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220075 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq626 y y x
       have i₂ := eq219947
       grind)
    | exact superpose eq219947 eq626
    | exact resolve eq626 eq219947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220250 : ∀ X0 : G, (M.op X0 X0) = (k y X0) ∨ (M.op X0 X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq219962 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219962
  have eq220251 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq219961 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219961
  have eq220319 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq220075 X0
       have i₂ := eq86 y X0
       grind)
    | exact superpose eq86 eq220075
    | exact resolve eq220075 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220075
  have eq224362 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq219966 X0
       have i₂ := eq220319 X0
       grind)
    | exact superpose eq220319 eq219966
    | exact resolve eq219966 eq220319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219966 eq220319
  have eq224860 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq224362 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224362
  have eq224899 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq224860 X1
       grind)
    | exact superpose eq224860 eq73
    | (have j1 := eq224860 X1
       grind)
    | exact resolve eq73 eq224860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225008 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq626 x x x
       have i₂ := eq224860 X0
       grind)
    | exact superpose eq224860 eq626
    | (have j1 := eq224860 X1
       grind)
    | exact resolve eq626 eq224860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224860
  have eq225255 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq225008 X0 X1
       have i₂ := eq86 x X0
       grind)
    | exact superpose eq86 eq225008
    | (have j0 := eq225008 X0 X1
       grind)
    | exact resolve eq225008 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225008
  have eq231641 : ∀ X0 X1 X2 : G, (M.op y X2) = X2 ∨ (M.op y X1) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq224899 X0 X2
       have i₂ := eq225255 X0 X1
       grind)
    | exact superpose eq225255 eq224899
    | (have j0 := eq224899 X0 X2
       have j1 := eq225255 X0 X2
       grind)
    | exact resolve eq224899 eq225255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224899 eq225255
  have eq251793 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq231641 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231641
  have eq251794 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq251793 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251793
  have eq251823 : ∀ X0 X1 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74 y X0
       have i₂ := eq251794 y X1
       grind)
    | exact superpose eq251794 eq74
    | (have j1 := eq251794 X0 X1
       grind)
    | exact resolve eq74 eq251794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq252660 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq251823 X0 X1
       have i₂ := eq86 y X0
       grind)
    | exact superpose eq86 eq251823
    | (have j0 := eq251823 X0 X1
       grind)
    | exact resolve eq251823 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251823
  have eq255947 : ∀ X0 X1 X2 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq252660 X0 X1
       have i₂ := eq251794 X0 X2
       grind)
    | exact superpose eq251794 eq252660
    | (have j0 := eq252660 X0 X1
       have j1 := eq251794 X0 X1
       grind)
    | exact resolve eq252660 eq251794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251794 eq252660
  have eq308022 : ∀ X0 : G, y ≠ y ∨ (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq255947 x X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255947
  have eq308023 : ∀ X0 : G, y = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq308022 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308022
  have eq308428 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq308023 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308023
  have eq308429 : y = (M.op x y) := by grind
  clear eq308428
  have eq437509 : ∀ X0 : G, (k y X0) = (k X0 y) ∨ (k X0 y) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq220250 X0
       have i₂ := eq220251 X0
       grind)
    | exact superpose eq220251 eq220250
    | (have j0 := eq220250 x
       grind)
    | exact resolve eq220250 eq220251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220250
  have eq440019 : ∀ X0 : G, (k y X0) = (k X0 y) ∨ (k X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq437509 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437509
  have eq447473 : ∀ X0 : G, (M.op X0 X0) = (k y X0) ∨ x = (M.op x x) ∨ (k X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq220251 X0
       have i₂ := eq440019 X0
       grind)
    | (have i₁ := eq220251 y
       have i₂ := eq440019 y
       grind)
    | exact superpose eq440019 eq220251
    | (have j1 := eq440019 X0
       grind)
    | exact resolve eq220251 eq440019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220251 eq440019
  have eq447694 : ∀ X0 : G, (M.op X0 X0) = (k y X0) ∨ x = (M.op x x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq447473 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447473
  have eq454391 : y ≠ (M.op y y) ∨ x = (M.op x x) ∨ y = (k y y) := by
    first
    | (have j0 := eq447694 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447694
  have eq454481 : y = (k y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq454391
       have r₂ := eq219947
       grind)
    | exact resolve eq454391 eq219947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219947 eq454391
  have eq454986 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26435 y
       have i₂ := eq454481
       grind)
    | exact superpose eq454481 eq26435
    | (have j0 := eq26435 y
       grind)
    | exact resolve eq26435 eq454481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454481
  have eq455237 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq454986
  have eq457304 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq73 (σ y) X0
       have i₂ := eq455237
       grind)
    | exact superpose eq455237 eq73
    | exact resolve eq73 eq455237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457420 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq626 (σ y) (σ y) x
       have i₂ := eq455237
       grind)
    | exact superpose eq455237 eq626
    | exact resolve eq626 eq455237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455237
  have eq457859 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq457420 X0
       have i₂ := eq86 (σ y) X0
       grind)
    | exact superpose eq86 eq457420
    | exact resolve eq457420 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457420
  have eq688576 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq457304 X0
       have i₂ := eq457859 X0
       grind)
    | exact superpose eq457859 eq457304
    | exact resolve eq457304 eq457859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457304
  have eq689442 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq688576 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688576
  have eq689487 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq457859 X0
       have i₂ := eq689442 X0
       grind)
    | exact superpose eq689442 eq457859
    | exact resolve eq457859 eq689442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457859 eq689442
  have eq691017 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq689487 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689487
  have eq697023 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq691017 (σ x)
       grind)
    | exact superpose eq691017 eq16
    | exact resolve eq16 eq691017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691017
  have eq697243 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq697023
       have i₂ := eq308429
       grind)
    | exact superpose eq308429 eq697023
    | exact resolve eq697023 eq308429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697023
  have eq697244 : x = (M.op x x) := by grind
  clear eq697243
  have eq697306 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq697244
       grind)
    | exact superpose eq697244 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq697244
       grind)
    | exact resolve eq12 eq697244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697311 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73 x X0
       have i₂ := eq697244
       grind)
    | exact superpose eq697244 eq73
    | exact resolve eq73 eq697244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697422 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq626 x x x
       have i₂ := eq697244
       grind)
    | exact superpose eq697244 eq626
    | exact resolve eq626 eq697244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697838 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq697306 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697306
  have eq698023 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq697422 X0
       have i₂ := eq86 x X0
       grind)
    | exact superpose eq86 eq697422
    | exact resolve eq697422 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq697422
  have eq698137 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 x) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X1
       have i₂ := eq697838 X0
       grind)
    | exact superpose eq697838 eq73
    | exact resolve eq73 eq697838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq700797 : (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26435 x
       have i₂ := eq697838 x
       grind)
    | exact superpose eq697838 eq26435
    | (have j0 := eq26435 x
       grind)
    | exact resolve eq26435 eq697838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26435
  have eq701095 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq700797
       have i₂ := eq697244
       grind)
    | exact superpose eq697244 eq700797
    | exact resolve eq700797 eq697244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697244 eq700797
  have eq701096 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq701095
  have eq701358 : (σ x) = (k (σ x) x) := by
    first
    | (have i₁ := eq701096
       have i₂ := eq697838 (σ x)
       grind)
    | exact superpose eq697838 eq701096
    | exact resolve eq701096 eq697838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697838 eq701096
  have eq733589 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq697311 X0
       have i₂ := eq698023 X0
       grind)
    | exact superpose eq698023 eq697311
    | exact resolve eq697311 eq698023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697311 eq698023
  have eq733754 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq626 x X1 X0
       have i₂ := eq733589 X0
       grind)
    | exact superpose eq733589 eq626
    | exact resolve eq626 eq733589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq735845 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq733754 X0 X0
       have i₂ := eq733589 X0
       grind)
    | exact superpose eq733589 eq733754
    | exact resolve eq733754 eq733589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733589 eq733754
  have eq877831 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq698137 (σ x) X0
       have i₂ := eq701358
       grind)
    | exact superpose eq701358 eq698137
    | exact resolve eq698137 eq701358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698137 eq701358
  have eq878735 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq877831 X0
       have i₂ := eq735845 X0 (σ x)
       grind)
    | exact superpose eq735845 eq877831
    | exact resolve eq877831 eq735845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735845 eq877831
  have eq881436 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq878735 (σ y)
       grind)
    | exact superpose eq878735 eq16
    | exact resolve eq16 eq878735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878735
  have eq883675 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq881436
       have i₂ := eq308429
       grind)
    | exact superpose eq308429 eq881436
    | exact resolve eq881436 eq308429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308429 eq881436
  have eq883676 : False := by grind
  exact eq883676

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq33 : ∀ X0 X1 X2 : G, (k (τ X2) (k (τ X0) X1)) = (τ (k X2 (k X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq23
    | exact resolve eq23 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq52
    | exact resolve eq52 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq74 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq95 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq74
    | exact resolve eq74 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq215 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq214 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq372 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq215 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq373 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq372 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq375 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq373 (σ X0)
       grind)
    | exact superpose eq373 eq29
    | exact resolve eq29 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq530 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq72
    | exact resolve eq72 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq723 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq16
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k X0 (τ (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq375 x
       have i₂ := eq85 x x
       grind)
    | exact superpose eq85 eq375
    | (have j1 := eq85 X0 X0
       grind)
    | exact resolve eq375 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq85 X0 X0
       grind)
    | exact superpose eq85 eq68
    | (have j1 := eq85 X0 X0
       grind)
    | exact resolve eq68 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq85 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq749 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq748 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq759 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq738 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq762 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k X0 (τ (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq724 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq766 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq762 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq762
    | (have j0 := eq762 X0
       grind)
    | exact resolve eq762 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq778 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq749 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq749
    | (have j0 := eq749 (τ X0)
       grind)
    | exact resolve eq749 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq749
  have eq789 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq778 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq778
    | (have j0 := eq778 X0
       grind)
    | exact resolve eq778 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq796 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq789 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq789
    | (have j0 := eq789 X0
       grind)
    | exact resolve eq789 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq1385 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (k (τ X0) (τ X0))
       have i₂ := eq766 (τ X0)
       grind)
    | exact superpose eq766 eq18
    | (have j1 := eq766 (τ X0)
       grind)
    | exact resolve eq18 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq1395 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k X0 (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1385 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1385
    | (have j0 := eq1385 X0
       grind)
    | exact resolve eq1385 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1385
  have eq1411 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1395 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1395
    | (have j0 := eq1395 X0
       grind)
    | exact resolve eq1395 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq1424 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1411 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1411
    | (have j0 := eq1411 X0
       grind)
    | exact resolve eq1411 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq2765 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq89 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2779 : ∀ X0 X1 X2 : G, (τ (k X2 (k X0 (σ X1)))) = (k (τ X2) (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X2 (M.op (τ X0) X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq23
    | (have j1 := eq89 X0 X1
       grind)
    | exact resolve eq23 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq2792 : ∀ X0 X1 X2 : G, (k (τ X2) (k (τ X0) X1)) = (k (τ X2) (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2779 X0 X1 X2
       have i₂ := eq33 X0 X1 X2
       grind)
    | exact superpose eq33 eq2779
    | (have j0 := eq2779 X0 X1 X2
       grind)
    | exact resolve eq2779 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq2779
  have eq2796 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2765 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2765
    | (have j0 := eq2765 X0 X1
       grind)
    | exact resolve eq2765 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765
  have eq6824 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq723
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq723
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq723 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq6827 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq6824
  have eq49635 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq375 y
       have i₂ := eq6827
       grind)
    | exact superpose eq6827 eq375
    | exact resolve eq375 eq6827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6827
  have eq49796 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq49635
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq49635
    | exact resolve eq49635 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49635
  have eq49801 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq796 y
       grind)
    | (have r₁ := eq49796
       have r₂ := eq796 y
       grind)
    | exact resolve eq49796 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq49796
  have eq49803 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq375 x
       have i₂ := eq49801
       grind)
    | exact superpose eq49801 eq375
    | exact resolve eq375 eq49801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq49880 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq95 (σ x) (σ x)
       have i₂ := eq49801
       grind)
    | exact superpose eq49801 eq95
    | exact resolve eq95 eq49801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49801
  have eq49943 : y = (k x y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq49803
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq49803
    | exact resolve eq49803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49803
  have eq49957 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2796 x y
       have i₂ := eq49943
       grind)
    | exact superpose eq49943 eq2796
    | (have j0 := eq2796 x y
       grind)
    | exact resolve eq2796 eq49943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2796 eq49943
  have eq49960 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq49957
  have eq52842 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49880
       grind)
    | exact superpose eq49880 eq16
    | exact resolve eq16 eq49880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49880
  have eq52926 : y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq52842
       have r₂ := eq49960
       grind)
    | exact resolve eq52842 eq49960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49960 eq52842
  have eq52933 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq74 y X0
       have i₂ := eq52926
       grind)
    | exact superpose eq52926 eq74
    | exact resolve eq74 eq52926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52939 : y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq373 y
       have i₂ := eq52926
       grind)
    | exact superpose eq52926 eq373
    | exact resolve eq373 eq52926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53011 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq530 y y x
       have i₂ := eq52926
       grind)
    | exact superpose eq52926 eq530
    | exact resolve eq530 eq52926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52926
  have eq53046 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq53011 X0
       have i₂ := eq95 y X0
       grind)
    | exact superpose eq95 eq53011
    | exact resolve eq53011 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53011
  have eq53086 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq759 y
       have i₂ := eq52939
       grind)
    | exact superpose eq52939 eq759
    | (have j0 := eq759 y
       grind)
    | exact resolve eq759 eq52939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759 eq52939
  have eq53207 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq53086
  have eq55846 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq74 (σ y) X0
       have i₂ := eq53207
       grind)
    | exact superpose eq53207 eq74
    | exact resolve eq74 eq53207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq55924 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq530 (σ y) (σ y) x
       have i₂ := eq53207
       grind)
    | exact superpose eq53207 eq530
    | exact resolve eq530 eq53207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq53207
  have eq55969 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq55924 X0
       have i₂ := eq95 (σ y) X0
       grind)
    | exact superpose eq95 eq55924
    | exact resolve eq55924 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55924
  have eq56781 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq52933 X0
       have i₂ := eq53046 X0
       grind)
    | exact superpose eq53046 eq52933
    | exact resolve eq52933 eq53046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52933
  have eq56938 : ∀ X0 : G, y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq56781 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56781
  have eq57365 : ∀ X0 : G, x = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 x
       have i₂ := eq56938 X0
       grind)
    | exact superpose eq56938 eq68
    | (have j1 := eq56938 x
       grind)
    | exact resolve eq68 eq56938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq56938
  have eq57578 : x ≠ x ∨ x = (M.op y x) := by
    first
    | (have j0 := eq57365 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57365
  have eq57579 : x = (M.op y x) := by grind
  clear eq57578
  have eq57582 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq53046 x
       have i₂ := eq57579
       grind)
    | exact superpose eq57579 eq53046
    | exact resolve eq53046 eq57579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53046 eq57579
  have eq72583 : ∀ X0 : G, (k (τ X0) (M.op (τ X0) (τ X0))) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1424 (τ X0)
       have i₂ := eq2792 X0 (τ X0) X0
       grind)
    | exact superpose eq2792 eq1424
    | (have j0 := eq1424 (τ X0)
       have j1 := eq2792 X0 (τ X0) x
       grind)
    | exact resolve eq1424 eq2792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424 eq2792
  have eq72825 : ∀ X0 : G, (k (τ X0) (M.op (τ X0) (τ X0))) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq72583 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72583
  have eq72977 : ∀ X0 : G, (k (τ X0) (M.op (τ X0) (τ X0))) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq72825 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq72825
    | (have j0 := eq72825 X0
       grind)
    | exact resolve eq72825 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq72825
  have eq73175 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq72977 X0
       have i₂ := eq373 (τ X0)
       grind)
    | exact superpose eq373 eq72977
    | (have j0 := eq72977 X0
       grind)
    | exact resolve eq72977 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq72977
  have eq73555 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq55846 X0
       have i₂ := eq55969 X0
       grind)
    | exact superpose eq55969 eq55846
    | exact resolve eq55846 eq55969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55846
  have eq73753 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq73555 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73555
  have eq73772 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq55969 X0
       have i₂ := eq73753 X0
       grind)
    | exact superpose eq73753 eq55969
    | exact resolve eq55969 eq73753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55969 eq73753
  have eq74079 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq73772 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73772
  have eq74642 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq74079 (σ x)
       grind)
    | exact superpose eq74079 eq16
    | exact resolve eq16 eq74079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74079
  have eq74713 : (σ y) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74642
       have i₂ := eq57582
       grind)
    | exact superpose eq57582 eq74642
    | exact resolve eq74642 eq57582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57582 eq74642
  have eq74719 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq74713
  have eq74720 : y = (M.op x x) := by grind
  clear eq74719
  have eq74789 : y = (M.op x y) := by
    first
    | (have i₁ := eq95 x x
       have i₂ := eq74720
       grind)
    | exact superpose eq74720 eq95
    | exact resolve eq95 eq74720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115084 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73175 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73175
    | exact resolve eq73175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73175
  have eq115402 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq115084 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq115084
    | (have j0 := eq115084 X0
       grind)
    | exact resolve eq115084 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq115084
  have eq115417 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have j0 := eq115402 X0
       have j1 := eq12 (τ (σ X0)) X0
       grind)
    | (have r₁ := eq115402 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq115402 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115402
  have eq115422 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq115417 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq115417
    | exact resolve eq115417 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115417
  have eq115687 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq115422 (σ X0)
       grind)
    | exact superpose eq115422 eq15
    | exact resolve eq15 eq115422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115799 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq115687 X0
       have i₂ := eq115422 X0
       grind)
    | exact superpose eq115422 eq115687
    | exact resolve eq115687 eq115422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115422 eq115687
  have eq116642 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq95 (σ X0) (σ X0)
       have i₂ := eq115799 X0
       grind)
    | exact superpose eq115799 eq95
    | exact resolve eq95 eq115799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq115799
  have eq119984 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq116642 x
       have i₂ := eq74720
       grind)
    | exact superpose eq74720 eq116642
    | exact resolve eq116642 eq74720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74720 eq116642
  have eq120366 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq119984
       grind)
    | exact superpose eq119984 eq16
    | exact resolve eq16 eq119984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119984
  have eq120581 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq120366
       have i₂ := eq74789
       grind)
    | exact superpose eq74789 eq120366
    | exact resolve eq120366 eq74789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74789 eq120366
  have eq120582 : False := by grind
  exact eq120582
