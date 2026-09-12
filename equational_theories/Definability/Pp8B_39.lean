import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_pyy_y_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  clear eq24
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
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq60 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq84
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq84
       grind)
    | exact superpose eq84 eq16
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op y x) ∨ (M.op x x) = (k y x) := by
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
  have eq99 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq500 X0
       grind)
    | exact superpose eq500 eq14
    | exact resolve eq14 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq579 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) X5)) X1) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq58 X1 (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X0 X5
       have i₂ := eq61 X3 X2 X4 X0
       grind)
    | exact superpose eq61 eq58
    | exact resolve eq58 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq61
  have eq892 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq507 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq507
    | exact resolve eq507 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq896 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60 eq507
    | exact resolve eq507 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq507
  have eq923 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq896 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9493 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) (M.op X0 X4)) (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq579 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X1 X0 X2 X4
       have i₂ := eq14 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq14 eq579
    | exact resolve eq579 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq9529 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op X0 X3) (M.op X0 X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9493 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq9493
    | exact resolve eq9493 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9493
  have eq18972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18973 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18972
    | exact resolve eq18972 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18972
  have eq18984 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq18973
       have r₂ := eq27
       grind)
    | exact resolve eq18973 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18973
  have eq18986 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18984
    | exact resolve eq18984 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18984
  have eq18989 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18986 eq99
    | (have r₁ := eq99
       have r₂ := eq18986
       grind)
    | exact resolve eq99 eq18986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18986
  have eq19072 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq18989
  have eq19073 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq19072
  have eq20074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq19073 eq97
    | exact resolve eq97 eq19073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq19073
  have eq20083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq20074
  have eq20086 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq20083
       have r₂ := eq27
       grind)
    | exact resolve eq20083 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20083
  have eq20088 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20086 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20086
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20086
       grind)
    | exact resolve eq13 eq20086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20086
  have eq20140 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq20088
  have eq20291 : (τ (σ x)) = (k y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20140 eq94
    | exact resolve eq94 eq20140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20140
  have eq20311 : x = (k y x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28 eq20291
    | exact resolve eq20291 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20291
  have eq20314 : (M.op x y) = (M.op x x) ∨ x = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq20311
       have r₂ := eq13 y x
       grind)
    | exact resolve eq20311 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20311
  have eq20316 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y x) ∨ (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq20314
       grind)
    | exact superpose eq20314 eq98
    | (have r₁ := eq98
       have r₂ := eq20314
       grind)
    | exact resolve eq98 eq20314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq20346 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq20314
       grind)
    | exact superpose eq20314 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq20314
       grind)
    | exact resolve eq12 eq20314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20314
  have eq20398 : x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ x = (k y x) := by grind
  clear eq20346
  have eq20399 : y = (M.op y x) ∨ (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq20316
  have eq20403 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq20399
       have r₂ := eq13 y x
       grind)
    | exact resolve eq20399 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20399
  have eq20430 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq20403
       grind)
    | exact superpose eq20403 eq84
    | exact resolve eq84 eq20403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20441 : x ≠ (M.op x y) ∨ x = (k y x) := by grind
  clear eq20403
  have eq20450 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq20 eq20430
    | exact resolve eq20430 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20430
  have eq20735 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq20450 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq20450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20450
  have eq20736 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq26 eq20735
    | exact resolve eq20735 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20735
  have eq20747 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have r₁ := eq20736
       have r₂ := eq27
       grind)
    | exact resolve eq20736 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20736
  have eq20749 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq26 eq20747
    | exact resolve eq20747 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20747
  have eq21248 : (M.op x y) = (k x x) ∨ x = (k y x) := by
    first
    | (have r₁ := eq20398
       have r₂ := eq20441
       grind)
    | exact resolve eq20398 eq20441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20398 eq20441
  have eq21310 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq21248
       grind)
    | exact superpose eq21248 eq43
    | exact resolve eq43 eq21248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq21248
  have eq21330 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq20 eq21310
    | exact resolve eq21310 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21310
  have eq21331 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21330
       have i₂ := eq100 sF2
       grind)
    | exact superpose eq100 eq21330
    | (have j1 := eq100 (σ x)
       grind)
    | exact resolve eq21330 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21330
  have eq24327 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | exact superpose eq20749 eq21331
    | exact resolve eq21331 eq20749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20749 eq21331
  have eq24421 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq24327
  have eq24460 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq24421
       have r₂ := eq27
       grind)
    | exact resolve eq24421 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24421
  have eq24471 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24460 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq24460
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq24460
       grind)
    | exact resolve eq13 eq24460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24460
  have eq24523 : (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24471
  have eq24683 : (τ (σ x)) = (k y x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24523 eq94
    | exact resolve eq94 eq24523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq24523
  have eq24723 : x = (k y x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq24683
    | exact resolve eq24683 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24683
  have eq24724 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24723
  have eq24733 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq24724
       grind)
    | exact superpose eq24724 eq84
    | exact resolve eq84 eq24724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq24724
  have eq24755 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24733
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24733
    | exact resolve eq24733 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24733
  have eq24822 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24755 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq24755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24827 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq24822
    | exact resolve eq24822 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24822
  have eq24828 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq24827
  have eq24840 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq24828
    | exact resolve eq24828 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24828
  have eq26093 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq24840 eq99
    | (have r₁ := eq99
       have r₂ := eq24840
       grind)
    | exact resolve eq99 eq24840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq24840
  have eq26184 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26093
  have eq26185 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26184
  have eq32842 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26185 eq24755
    | exact resolve eq24755 eq26185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24755 eq26185
  have eq32849 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq32842
  have eq32869 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32849 eq14
    | exact resolve eq14 eq32849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32915 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32849 eq892
    | exact resolve eq892 eq32849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32923 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32849 eq9529
    | exact resolve eq9529 eq32849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9529
  have eq32930 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq32923 x
       have i₂ := eq892 sF3 x
       grind)
    | exact superpose eq892 eq32923
    | exact resolve eq32923 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32923
  have eq32959 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq32869 x
       have i₂ := eq892 sF3 x
       grind)
    | exact superpose eq892 eq32869
    | exact resolve eq32869 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892 eq32869
  have eq34417 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32915 eq32959
    | exact resolve eq32959 eq32915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32915 eq32959
  have eq34525 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34417
  have eq34810 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34525 eq32849
    | exact resolve eq32849 eq34525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32849
  have eq34813 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34525 eq32930
    | exact resolve eq32930 eq34525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32930 eq34525
  have eq34873 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34813
  have eq34876 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq34810
  have eq34884 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq34873
    | exact resolve eq34873 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34873
  have eq35270 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34884
  have eq35272 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq35270
       have r₂ := eq34876
       grind)
    | exact resolve eq35270 eq34876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34876 eq35270
  have eq35277 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq35272 eq27
    | exact resolve eq27 eq35272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq35315 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq35272 eq896
    | exact resolve eq896 eq35272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq35316 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq35272 eq923
    | (have r₁ := eq923
       have r₂ := eq35272
       grind)
    | exact resolve eq923 eq35272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq35332 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq35316
  have eq35369 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq35315 eq57
    | exact resolve eq57 eq35315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq35516 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq35272 eq35369
    | exact resolve eq35369 eq35272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35369
  have eq35545 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35315 eq35516
    | exact resolve eq35516 eq35315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35315 eq35516
  have eq35556 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq35545
    | exact resolve eq35545 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq35545
  have eq35563 : (σ x) = (σ y) := by
    first
    | exact superpose eq35272 eq35556
    | exact resolve eq35556 eq35272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35272 eq35556
  have eq35811 : y = (τ (σ x)) := by
    first
    | exact superpose eq35563 eq29
    | exact resolve eq29 eq35563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq35563
  have eq36042 : x = y := by
    first
    | exact superpose eq28 eq35811
    | exact resolve eq35811 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35811
  have eq36067 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq36042
       grind)
    | exact superpose eq36042 eq18
    | exact resolve eq18 eq36042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq36042
  have eq36287 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq35332 eq49
    | exact resolve eq49 eq35332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq35332
  have eq36323 : x = (k x x) := by
    first
    | exact superpose eq28 eq36287
    | exact resolve eq36287 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq36287
  have eq36366 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq100 x
       have i₂ := eq36323
       grind)
    | exact superpose eq36323 eq100
    | (have j0 := eq100 x
       grind)
    | exact resolve eq100 eq36323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq36323
  have eq36367 : x = (M.op x x) := by grind
  clear eq36366
  have eq37103 : x = (M.op x y) := by
    first
    | (have i₁ := eq36067
       have i₂ := eq36367
       grind)
    | exact superpose eq36367 eq36067
    | exact resolve eq36067 eq36367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36067 eq36367
  have eq37104 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq37103 eq20
    | exact resolve eq20 eq37103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq37103
  have eq37341 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37104
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37104
    | exact resolve eq37104 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37104
  have eq37416 : False := by grind
  exact eq37416

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_pyy_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq188 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq195 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq190 eq16
    | exact resolve eq16 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq183 eq188
    | exact resolve eq188 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq188
  have eq561 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq556
       grind)
    | exact superpose eq556 eq16
    | exact resolve eq16 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq568 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq190 eq195
    | exact resolve eq195 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq195
  have eq573 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ y) (σ y)) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq568 eq16
    | exact resolve eq16 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq581 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq561 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq561
    | exact resolve eq561 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq630 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq631 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq687 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq726 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq573 (M.op sF3 x)
       have i₂ := eq16 sF3 sF3 x
       grind)
    | exact superpose eq16 eq573
    | exact resolve eq573 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq799 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq630
       grind)
    | exact superpose eq630 eq39
    | exact resolve eq39 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq799
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq799
    | exact resolve eq799 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq802 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq800
    | exact resolve eq800 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq868 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq199
    | exact resolve eq199 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq891 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq868 X0
       grind)
    | exact superpose eq868 eq16
    | exact resolve eq16 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq892 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X0) X1
       have i₂ := eq868 X0
       grind)
    | exact superpose eq868 eq16
    | exact resolve eq16 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq935 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq891 (M.op X1 X0) X0
       have i₂ := eq16 X0 X1 X0
       grind)
    | exact superpose eq16 eq891
    | exact resolve eq891 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq943 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq891 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq891
    | exact resolve eq891 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq177 eq891
    | exact resolve eq891 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq951 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq178 eq891
    | exact resolve eq891 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq947 eq12
    | (have j0 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq947
       grind)
    | exact resolve eq12 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq971 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq967
  have eq978 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq951 eq12
    | (have j0 := eq12 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq951
       grind)
    | exact resolve eq12 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq981 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq951 eq16
    | exact resolve eq16 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq982 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq978
  have eq1369 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq971 eq39
    | exact resolve eq39 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq971
  have eq1370 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq20 eq1369
    | exact resolve eq1369 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1373 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) x) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq982 eq141
    | exact resolve eq141 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1663 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq802 eq631
    | exact resolve eq631 eq802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq1670 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1663
       have r₂ := eq27
       grind)
    | exact resolve eq1663 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1663
  have eq1679 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1670 eq16
    | exact resolve eq16 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1686 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1670 eq943
    | exact resolve eq943 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1691 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq726 eq1679
    | exact resolve eq1679 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq1679
  have eq2163 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1686 eq1691
    | exact resolve eq1691 eq1686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686
  have eq2186 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq2163
  have eq2194 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2186 eq1670
    | exact resolve eq1670 eq2186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670
  have eq2200 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ x)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2186 eq16
    | exact resolve eq16 eq2186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2186
  have eq2211 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq2194
  have eq2215 : ∀ X0 : G, y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1691 eq2200
    | exact resolve eq2200 eq1691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691 eq2200
  have eq2227 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq2211
       grind)
    | exact superpose eq2211 eq16
    | exact resolve eq16 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2242 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2227 X0
       have i₂ := eq581 X0
       grind)
    | exact superpose eq581 eq2227
    | exact resolve eq2227 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581 eq2227
  have eq2549 : ∀ X0 : G, y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq943 y x
       have i₂ := eq2215 X0
       grind)
    | exact superpose eq2215 eq943
    | (have j1 := eq2215 (σ y)
       grind)
    | exact resolve eq943 eq2215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2215
  have eq2594 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2242 x
       have i₂ := eq2211
       grind)
    | exact superpose eq2211 eq2242
    | exact resolve eq2242 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211
  have eq2617 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq2594
  have eq3295 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq2617
       grind)
    | exact superpose eq2617 eq16
    | exact resolve eq16 eq2617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2617
  have eq3324 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2242 eq3295
    | exact resolve eq3295 eq2242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242 eq3295
  have eq3436 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3324 y
       grind)
    | exact superpose eq3324 eq18
    | (have j1 := eq3324 y
       grind)
    | exact resolve eq18 eq3324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3324
  have eq3462 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq3436
  have eq4024 : ∀ X0 : G, y ≠ y ∨ y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2549 X0
       grind)
    | exact superpose eq2549 eq13
    | (have j1 := eq2549 (σ y)
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq2549 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq2549 (σ x)
       grind)
    | exact resolve eq13 eq2549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2549
  have eq4042 : ∀ X0 : G, y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4024 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4024
  have eq5060 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40 y
       have i₂ := eq4042 X0
       grind)
    | exact superpose eq4042 eq40
    | (have j1 := eq4042 (σ y)
       grind)
    | exact resolve eq40 eq4042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4042
  have eq5076 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5060 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5060
    | (have j0 := eq5060 (σ y)
       grind)
    | exact resolve eq5060 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5060
  have eq5078 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq3462 eq5076
    | (have j0 := eq5076 (σ y)
       grind)
    | exact resolve eq5076 eq3462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3462 eq5076
  have eq5728 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq686 X0 x
       have i₂ := eq5078 (k x X0)
       grind)
    | exact superpose eq5078 eq686
    | (have j0 := eq686 (σ x) (σ x)
       have j1 := eq5078 (σ x)
       grind)
    | (have r₁ := eq686 (σ x) (σ x)
       have r₂ := eq5078 X0
       grind)
    | exact resolve eq686 eq5078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5078
  have eq5729 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5728 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5728
  have eq5730 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5729 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5729
  have eq6064 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq5730 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5730
  have eq6065 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6064
  have eq6129 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6065 eq892
    | exact resolve eq892 eq6065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq6130 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6065 eq891
    | exact resolve eq891 eq6065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891 eq6065
  have eq6143 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6129 x
       have i₂ := eq943 sF2 x
       grind)
    | exact superpose eq943 eq6129
    | exact resolve eq6129 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6129
  have eq6561 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6143 eq6130
    | exact resolve eq6130 eq6143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6130 eq6143
  have eq6592 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq6561 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6561
  have eq6667 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6592 eq26
    | (have j1 := eq6592 (σ y)
       grind)
    | exact resolve eq26 eq6592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6592
  have eq6697 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6667
  have eq6722 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ y)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6697 eq178
    | exact resolve eq178 eq6697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq6742 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ x) X0)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6697 eq981
    | exact resolve eq981 eq6697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq6743 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6697 eq982
    | exact resolve eq982 eq6697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq6744 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6697 eq1373
    | exact resolve eq1373 eq6697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq6746 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq6744
    | exact resolve eq6744 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq6744
  have eq7064 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6746 eq935
    | exact resolve eq935 eq6746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7073 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq7064
    | exact resolve eq7064 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7064
  have eq7084 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6697 eq7073
    | exact resolve eq7073 eq6697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6697 eq7073
  have eq7192 : (σ x) = (σ y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7084 eq6746
    | exact resolve eq6746 eq7084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6746 eq7084
  have eq7221 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq7192
  have eq7263 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq630
       have i₂ := eq7221
       grind)
    | exact superpose eq7221 eq630
    | exact resolve eq630 eq7221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq7271 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq7263
  have eq7299 : y ≠ y ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq7271
       grind)
    | exact superpose eq7271 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq7271
       grind)
    | exact resolve eq13 eq7271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7271
  have eq7318 : (k y x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq7299
  have eq7335 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7221 eq7318
    | exact resolve eq7318 eq7221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7221 eq7318
  have eq7492 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq943 x x
       have i₂ := eq7335
       grind)
    | exact superpose eq7335 eq943
    | exact resolve eq943 eq7335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7335
  have eq7509 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7492
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7492
    | exact resolve eq7492 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7492
  have eq7510 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq7509
  have eq7560 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7510 eq6722
    | exact resolve eq6722 eq7510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6722
  have eq7562 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7510 eq6742
    | exact resolve eq6742 eq7510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6742
  have eq7563 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7510 eq6743
    | exact resolve eq6743 eq7510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6743 eq7510
  have eq7572 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq7563
  have eq7573 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7562 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7562
  have eq7576 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7560 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7560
  have eq7589 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq688 (σ x)
       grind)
    | (have r₁ := eq7572
       have r₂ := eq688 (σ x)
       grind)
    | exact resolve eq7572 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq7572
  have eq7590 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7573 x
       have i₂ := eq943 sF2 x
       grind)
    | exact superpose eq943 eq7573
    | exact resolve eq7573 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7573
  have eq7743 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7589 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq7589
       grind)
    | exact resolve eq13 eq7589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7749 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq7589 eq179
    | exact resolve eq179 eq7589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq7589
  have eq7762 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq7743
  have eq7781 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) X1) X0) X1) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq7590 eq7749
    | exact resolve eq7749 eq7590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7749
  have eq7803 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7762 eq141
    | exact resolve eq141 eq7762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq7762
  have eq7820 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq7803
    | exact resolve eq7803 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq7803
  have eq7832 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq686 x x
       have i₂ := eq7820
       grind)
    | exact superpose eq7820 eq686
    | (have j0 := eq686 x x
       grind)
    | (have r₁ := eq686 x x
       have r₂ := eq7820
       grind)
    | exact resolve eq686 eq7820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq7820
  have eq7833 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq7832
  have eq7834 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq7833
  have eq7866 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq7834
       grind)
    | exact superpose eq7834 eq16
    | exact resolve eq16 eq7834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7834
  have eq8927 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7590 eq7576
    | exact resolve eq7576 eq7590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7576 eq7590
  have eq8964 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8927 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8927
  have eq9638 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8964 eq7781
    | exact resolve eq7781 eq8964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7781 eq8964
  have eq9716 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq9638 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9638
  have eq10599 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7866 X0
       have i₂ := eq9716 x X0
       grind)
    | exact superpose eq9716 eq7866
    | exact resolve eq7866 eq9716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7866 eq9716
  have eq10641 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq10599 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10599
  have eq10701 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10641 y
       grind)
    | exact superpose eq10641 eq18
    | (have j1 := eq10641 y
       grind)
    | exact resolve eq18 eq10641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10641
  have eq10741 : y = (M.op x y) := by grind
  clear eq10701
  have eq10760 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq10741
       grind)
    | exact superpose eq10741 eq24
    | exact resolve eq24 eq10741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10741
  have eq10787 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10760 eq20
    | exact resolve eq20 eq10760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10867 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq10787 eq1370
    | exact resolve eq1370 eq10787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq11431 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq10867 eq631
    | exact resolve eq631 eq10867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq11441 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq11431
  have eq14166 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq11441 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq11441
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq11441
       grind)
    | exact resolve eq13 eq11441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11441
  have eq14186 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq14166
  have eq14199 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq10867 eq14186
    | exact resolve eq14186 eq10867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10867 eq14186
  have eq14357 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq14199 eq943
    | exact resolve eq943 eq14199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943 eq14199
  have eq14378 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq26 eq14357
    | exact resolve eq14357 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14357
  have eq14379 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14378
  have eq14420 : x = (M.op (M.op x (M.op x y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14379 eq935
    | exact resolve eq935 eq14379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq14436 : x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq947 eq14420
    | exact resolve eq14420 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14420
  have eq14448 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14379 eq14436
    | exact resolve eq14436 eq14379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14379 eq14436
  have eq14457 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14448 eq27
    | exact resolve eq27 eq14448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14448
  have eq14488 : x = (M.op x y) := by
    first
    | (have r₁ := eq14457
       have r₂ := eq10787
       grind)
    | exact resolve eq14457 eq10787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14457
  have eq14491 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq14488
       grind)
    | exact superpose eq14488 eq22
    | exact resolve eq22 eq14488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq14502 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq947
       have i₂ := eq14488
       grind)
    | exact superpose eq14488 eq947
    | exact resolve eq947 eq14488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947 eq14488
  have eq14572 : (σ x) = (σ y) := by
    first
    | exact superpose eq14491 eq10760
    | exact resolve eq10760 eq14491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10760
  have eq14573 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14491 eq20
    | exact resolve eq20 eq14491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14491
  have eq14673 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14572 eq26
    | exact resolve eq26 eq14572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq15288 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq14502 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq14502
       grind)
    | exact resolve eq13 eq14502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14502
  have eq15307 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq15288
  have eq15328 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15307 eq37
    | exact resolve eq37 eq15307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq15307
  have eq15347 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15328
    | exact resolve eq15328 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq15328
  have eq15355 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq10787 eq15347
    | exact resolve eq15347 eq10787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10787 eq15347
  have eq15363 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq14572 eq15355
    | exact resolve eq15355 eq14572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14572 eq15355
  have eq15430 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14673 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq14673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14673
  have eq15451 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15430
  have eq15457 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15363 eq15451
    | exact resolve eq15451 eq15363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15363 eq15451
  have eq15458 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15457
  have eq15466 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq15458 eq27
    | exact resolve eq27 eq15458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15458
  have eq15530 : False := by grind
  exact eq15530

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then X else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_x_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
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
  have eq39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq39 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq39
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq9
    | exact resolve eq9 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq9
    | exact resolve eq9 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 X1 (M.op X0 X0) X0 X2
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq39
    | exact resolve eq39 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq193 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq122 (M.op X1 X0) X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq122
    | exact resolve eq122 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq212 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq123
    | exact resolve eq123 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 X1) X0
       have i₂ := eq212 X0 X1
       grind)
    | exact superpose eq212 eq64
    | (have j0 := eq64 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq64 (M.op X0 X1) X0
       have r₂ := eq212 X0 X1
       grind)
    | exact resolve eq64 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq243 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq262 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ X0) X1) X0
       have i₂ := eq253 (σ X0) X1
       grind)
    | exact superpose eq253 eq22
    | exact resolve eq22 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq253
  have eq411 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq1541 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq126
    | exact resolve eq126 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq1646 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq411 y x
       grind)
    | exact superpose eq411 eq16
    | (have j1 := eq411 y x
       grind)
    | exact resolve eq16 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1692 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq411 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq6701 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1692 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1692
    | (have j0 := eq1692 (τ X1) (τ X0)
       grind)
    | exact resolve eq1692 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq6778 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6701 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6701
    | (have j0 := eq6701 X0 X1
       grind)
    | exact resolve eq6701 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6701
  have eq6797 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6778 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6778
    | (have j0 := eq6778 X0 X1
       grind)
    | exact resolve eq6778 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6778
  have eq6809 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6797 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6797
    | (have j0 := eq6797 X0 X1
       grind)
    | exact resolve eq6797 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6797
  have eq6815 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6809 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6809
    | (have j0 := eq6809 X0 X1
       grind)
    | exact resolve eq6809 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6809
  have eq6820 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6815 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6815
    | (have j0 := eq6815 X0 X1
       grind)
    | exact resolve eq6815 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6815
  have eq6825 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6820 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6820
    | (have j0 := eq6820 X0 X1
       grind)
    | exact resolve eq6820 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6820
  have eq8289 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1646
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1646
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq1646 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq8290 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq8289
  have eq198712 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq8290
       grind)
    | exact superpose eq8290 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8290
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq8290
       grind)
    | exact resolve eq12 eq8290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8290
  have eq198913 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq198712
  have eq198994 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq64 (σ y) (σ x)
       grind)
    | (have r₁ := eq198913
       have r₂ := eq64 (σ y) (σ x)
       grind)
    | (have r₁ := eq198913
       have r₂ := eq64 y x
       grind)
    | exact resolve eq198913 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198913
  have eq199012 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq198994
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq198994
    | exact resolve eq198994 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198994
  have eq199031 : (k y x) = (τ (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq199012
       grind)
    | exact superpose eq199012 eq10
    | exact resolve eq10 eq199012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199012
  have eq199165 : y = (k y x) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq199031
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq199031
    | exact resolve eq199031 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199031
  have eq199166 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq6825 y x
       grind)
    | (have r₁ := eq199165
       have r₂ := eq6825 y x
       grind)
    | exact resolve eq199165 eq6825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199165
  have eq199167 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq199166
       grind)
    | exact superpose eq199166 eq9
    | exact resolve eq9 eq199166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199169 : y ≠ y ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq199166
       grind)
    | exact superpose eq199166 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq199166
       grind)
    | exact resolve eq12 eq199166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199370 : y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq199169
  have eq199446 : y = (k y x) := by
    first
    | (have j1 := eq64 y x
       grind)
    | (have r₁ := eq199370
       have r₂ := eq64 y x
       grind)
    | exact resolve eq199370 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq199370
  have eq199447 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq199167 X0
       have i₂ := eq212 y X0
       grind)
    | exact superpose eq212 eq199167
    | exact resolve eq199167 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199167
  have eq199465 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1692 x y
       have i₂ := eq199446
       grind)
    | exact superpose eq199446 eq1692
    | (have j0 := eq1692 x y
       grind)
    | exact resolve eq1692 eq199446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199446
  have eq199471 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq199465
  have eq203422 : (M.op y x) = (M.op x (M.op y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq193 x y
       have i₂ := eq199447 x
       grind)
    | exact superpose eq199447 eq193
    | exact resolve eq193 eq199447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq199447
  have eq207121 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq203422
       have i₂ := eq199166
       grind)
    | exact superpose eq199166 eq203422
    | exact resolve eq203422 eq199166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199166 eq203422
  have eq207351 : y = (M.op x y) := by grind
  clear eq207121
  have eq207356 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) y) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 x y X1
       have i₂ := eq207351
       grind)
    | exact superpose eq207351 eq39
    | exact resolve eq39 eq207351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq233645 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq262 y (σ x)
       have i₂ := eq199471
       grind)
    | exact superpose eq199471 eq262
    | exact resolve eq262 eq199471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq199471
  have eq234050 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq233645
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq233645
    | exact resolve eq233645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233645
  have eq234064 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq234050
       grind)
    | exact superpose eq234050 eq16
    | exact resolve eq16 eq234050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234050
  have eq234359 : (σ y) ≠ (σ y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq234064
       have i₂ := eq207351
       grind)
    | exact superpose eq207351 eq234064
    | exact resolve eq234064 eq207351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207351 eq234064
  have eq234360 : y = (k y y) := by grind
  clear eq234359
  have eq234567 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1692 y y
       have i₂ := eq234360
       grind)
    | exact superpose eq234360 eq1692
    | (have j0 := eq1692 y y
       grind)
    | exact resolve eq1692 eq234360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq234569 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6825 y y
       have i₂ := eq234360
       grind)
    | exact superpose eq234360 eq6825
    | (have j0 := eq6825 y y
       grind)
    | (have r₁ := eq6825 y y
       have r₂ := eq234360
       grind)
    | exact resolve eq6825 eq234360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6825 eq234360
  have eq234572 : y ≠ y ∨ y = (M.op y y) := by grind
  clear eq234569
  have eq234573 : y = (M.op y y) := by grind
  clear eq234572
  have eq234575 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq234567
  have eq234576 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq234575
  have eq234620 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq123 y X0
       have i₂ := eq234573
       grind)
    | exact superpose eq234573 eq123
    | exact resolve eq123 eq234573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234817 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq1541 y y x
       have i₂ := eq234573
       grind)
    | exact superpose eq234573 eq1541
    | exact resolve eq1541 eq234573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234573
  have eq234998 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq234817 X0
       have i₂ := eq212 y X0
       grind)
    | exact superpose eq212 eq234817
    | exact resolve eq234817 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq234817
  have eq238682 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq123 (σ y) X0
       have i₂ := eq234576
       grind)
    | exact superpose eq234576 eq123
    | exact resolve eq123 eq234576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq234576
  have eq239682 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq234620 X0
       have i₂ := eq234998 X0
       grind)
    | exact superpose eq234998 eq234620
    | exact resolve eq234620 eq234998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234620
  have eq239691 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq234998 X0
       have i₂ := eq239682 X0
       grind)
    | exact superpose eq239682 eq234998
    | exact resolve eq234998 eq239682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234998
  have eq239908 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1541 y X1 X0
       have i₂ := eq239682 X0
       grind)
    | exact superpose eq239682 eq1541
    | exact resolve eq1541 eq239682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541
  have eq240518 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq239908 X0 X0
       have i₂ := eq239682 X0
       grind)
    | exact superpose eq239682 eq239908
    | exact resolve eq239908 eq239682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239908
  have eq270496 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq238682 X0
       have i₂ := eq240518 X0 (σ y)
       grind)
    | exact superpose eq240518 eq238682
    | exact resolve eq238682 eq240518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238682 eq240518
  have eq270949 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (M.op x (σ y)) y) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq207356 (σ y) X0
       have i₂ := eq270496 (M.op (M.op (M.op x (σ y)) y) X0)
       grind)
    | exact superpose eq270496 eq207356
    | exact resolve eq207356 eq270496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207356 eq270496
  have eq271208 : ∀ X0 : G, (σ y) = (M.op (M.op y X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq270949 X0
       have i₂ := eq239691 (M.op x (σ y))
       grind)
    | exact superpose eq239691 eq270949
    | exact resolve eq270949 eq239691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270949
  have eq271415 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq271208 X0
       have i₂ := eq239682 X0
       grind)
    | exact superpose eq239682 eq271208
    | exact resolve eq271208 eq239682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239682 eq271208
  have eq272623 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq271415 (σ x)
       grind)
    | exact superpose eq271415 eq16
    | exact resolve eq16 eq271415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271415
  have eq272741 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq272623
       have i₂ := eq239691 x
       grind)
    | exact superpose eq239691 eq272623
    | exact resolve eq272623 eq239691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239691 eq272623
  have eq272742 : False := by grind
  exact eq272742

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_pyy_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq69 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq76 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq9
    | exact resolve eq9 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq9
    | exact resolve eq9 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq77
    | exact resolve eq77 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq106 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq9
    | exact resolve eq9 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1013 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    grind
  have eq1018 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1013 X0
       have i₂ := eq69 (τ X0)
       grind)
    | exact superpose eq69 eq1013
    | (have j0 := eq1013 X0
       grind)
    | exact resolve eq1013 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1013
  have eq60085 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq1018 (σ X0)
       grind)
    | exact superpose eq1018 eq23
    | (have j1 := eq1018 (σ X0)
       grind)
    | exact resolve eq23 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq60113 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq60085 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq60085
    | (have j0 := eq60085 X0
       grind)
    | exact resolve eq60085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60085
  have eq60136 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq60113 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60113
    | (have j0 := eq60113 X0
       grind)
    | exact resolve eq60113 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60113
  have eq60149 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq60136 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60136
    | (have j0 := eq60136 X0
       grind)
    | exact resolve eq60136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60136
  have eq129528 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (σ X1) X0
       have i₂ := eq201 X0 X1
       grind)
    | exact superpose eq201 eq91
    | (have j1 := eq201 (σ X0) X0
       grind)
    | exact resolve eq91 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129706 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq201 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq129707 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq129706 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129706
  have eq129718 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq129707 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq129707
    | (have j0 := eq129707 X0
       grind)
    | exact resolve eq129707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129707
  have eq129953 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq129718 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq129718
    | exact resolve eq129718 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129718
  have eq130185 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq129953 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq129953
    | (have j0 := eq129953 X0
       grind)
    | exact resolve eq129953 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129953
  have eq130355 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq130185 X0
       grind)
    | exact superpose eq130185 eq11
    | (have j1 := eq130185 X0
       grind)
    | exact resolve eq11 eq130185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130185
  have eq130559 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq130355 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq130355
    | (have j0 := eq130355 X0
       grind)
    | exact resolve eq130355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130355
  have eq130662 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq108 X0 X0
       have i₂ := eq130559 X0
       grind)
    | exact superpose eq130559 eq108
    | (have j1 := eq130559 X0
       grind)
    | (have r₁ := eq108 X0 X0
       have r₂ := eq130559 X0
       grind)
    | exact resolve eq108 eq130559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq130559
  have eq131005 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq130662 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130662
  have eq131006 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq131005 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131005
  have eq131763 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq131006 (σ X0)
       grind)
    | exact superpose eq131006 eq15
    | exact resolve eq15 eq131006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131775 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq131006 (τ X0)
       grind)
    | exact superpose eq131006 eq32
    | exact resolve eq32 eq131006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131866 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq131775 X0
       have i₂ := eq131006 X0
       grind)
    | exact superpose eq131006 eq131775
    | exact resolve eq131775 eq131006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131775
  have eq131878 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq131763 X0
       have i₂ := eq131006 X0
       grind)
    | exact superpose eq131006 eq131763
    | exact resolve eq131763 eq131006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131763
  have eq132331 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq131866 X0
       grind)
    | exact superpose eq131866 eq9
    | exact resolve eq9 eq131866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132910 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq76 (σ X0)
       have i₂ := eq131878 X0
       grind)
    | exact superpose eq131878 eq76
    | exact resolve eq76 eq131878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq132955 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60149 (σ X0)
       have i₂ := eq131878 X0
       grind)
    | exact superpose eq131878 eq60149
    | exact resolve eq60149 eq131878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60149
  have eq132991 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq131878 X0
       grind)
    | exact superpose eq131878 eq9
    | exact resolve eq9 eq131878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133017 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0) (σ X0)
       have i₂ := eq131878 X0
       grind)
    | exact superpose eq131878 eq91
    | exact resolve eq91 eq131878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133134 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq132955 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq132955
    | (have j0 := eq132955 X0
       grind)
    | exact resolve eq132955 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132955
  have eq133147 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq132910 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq132910
    | (have j0 := eq132910 X0
       grind)
    | exact resolve eq132910 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132910
  have eq136413 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (σ X0)) X1) (σ (σ (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq132991 (σ X0) X1
       have i₂ := eq131878 X0
       grind)
    | exact superpose eq131878 eq132991
    | exact resolve eq132991 eq131878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132991
  have eq168716 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k (M.op X0 X0) X0)) ∨ (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq133147 X0
       have i₂ := eq133134 X0
       grind)
    | exact superpose eq133134 eq133147
    | (have j0 := eq133147 X0
       have j1 := eq133134 X0
       grind)
    | (have r₁ := eq133147 X0
       have r₂ := eq133134 X0
       grind)
    | exact resolve eq133147 eq133134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133134 eq133147
  have eq168721 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq168716 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168716
  have eq217469 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq168721 (τ X0)
       have i₂ := eq19 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq168721
    | exact resolve eq168721 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168721
  have eq217800 : ∀ X0 : G, (σ (τ (M.op X0 X0))) = (k (σ (τ (M.op X0 X0))) X0) ∨ (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq217469 X0
       have i₂ := eq131866 X0
       grind)
    | exact superpose eq131866 eq217469
    | (have j0 := eq217469 X0
       grind)
    | exact resolve eq217469 eq131866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217469
  have eq217864 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq217800 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq217800
    | (have j0 := eq217800 X0
       grind)
    | exact resolve eq217800 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217800
  have eq217910 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ (M.op X0 X0))) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq217864 X0
       have i₂ := eq131866 X0
       grind)
    | exact superpose eq131866 eq217864
    | (have j0 := eq217864 X0
       grind)
    | exact resolve eq217864 eq131866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217864
  have eq217935 : ∀ X0 : G, (σ (τ X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq217910 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq217910
    | (have j0 := eq217910 X0
       grind)
    | exact resolve eq217910 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217910
  have eq217955 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq217935 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq217935
    | (have j0 := eq217935 X0
       grind)
    | exact resolve eq217935 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217935
  have eq218225 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq217955 (τ X0)
       have i₂ := eq131866 X0
       grind)
    | exact superpose eq131866 eq217955
    | exact resolve eq217955 eq131866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217955
  have eq218382 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k (M.op X0 X0) X0)) ∨ (τ X0) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq218225 X0
       have i₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact superpose eq32 eq218225
    | (have j0 := eq218225 X0
       grind)
    | exact resolve eq218225 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218225
  have eq218454 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k (M.op X0 X0) X0)) ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq218382 X0
       have i₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact superpose eq32 eq218382
    | (have j0 := eq218382 X0
       grind)
    | exact resolve eq218382 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218382
  have eq773094 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq129528 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq129528
    | exact resolve eq129528 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773702 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (k (σ X0) (σ X0))) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq218454 (σ X0)
       have i₂ := eq129528 X0 X1
       grind)
    | exact superpose eq129528 eq218454
    | (have j1 := eq129528 X0 X1
       grind)
    | exact resolve eq218454 eq129528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129528 eq218454
  have eq773887 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq773702 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773702
  have eq773967 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq773887 X0 X1
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq773887
    | (have j0 := eq773887 X0 X1
       grind)
    | exact resolve eq773887 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq773887
  have eq774233 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq773094 X0 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq773094
    | (have j0 := eq773094 X0 X0
       grind)
    | exact resolve eq773094 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq773094
  have eq774309 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq773967 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq773967
    | (have j0 := eq773967 X0 X1
       grind)
    | exact resolve eq773967 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773967
  have eq774498 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq774309 X0 X1
       have i₂ := eq131006 X0
       grind)
    | exact superpose eq131006 eq774309
    | (have j0 := eq774309 X0 X1
       grind)
    | exact resolve eq774309 eq131006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131006 eq774309
  have eq775039 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq774233 X1 X0
       grind)
    | exact superpose eq774233 eq11
    | (have j1 := eq774233 X1 X1
       grind)
    | exact resolve eq11 eq774233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774233
  have eq775688 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq775039 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq775039
    | (have j0 := eq775039 X1 X1
       grind)
    | exact resolve eq775039 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775039
  have eq777140 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq775688 (τ X0) X1
       grind)
    | exact superpose eq775688 eq19
    | (have j1 := eq775688 X1 X1
       grind)
    | exact resolve eq19 eq775688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775688
  have eq778255 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq777140 X0 X1
       have i₂ := eq131866 X0
       grind)
    | exact superpose eq131866 eq777140
    | (have j0 := eq777140 X0 X1
       grind)
    | exact resolve eq777140 eq131866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131866 eq777140
  have eq783751 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq778255 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq778255
    | (have j0 := eq778255 (σ X0) X1
       grind)
    | exact resolve eq778255 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778255
  have eq784982 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq783751 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq783751
    | (have j0 := eq783751 X0 X1
       grind)
    | exact resolve eq783751 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783751
  have eq785269 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq784982 X0 X1
       have i₂ := eq131878 X0
       grind)
    | exact superpose eq131878 eq784982
    | (have j0 := eq784982 X0 X1
       grind)
    | exact resolve eq784982 eq131878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784982
  have eq785411 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq785269 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq785269
    | (have j0 := eq785269 X0 X1
       grind)
    | exact resolve eq785269 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785269
  have eq790940 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 (σ X0))
       have i₂ := eq774498 X0 X1
       grind)
    | exact superpose eq774498 eq11
    | (have j1 := eq774498 X0 X1
       grind)
    | exact resolve eq11 eq774498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774498
  have eq791438 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq790940 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq790940
    | (have j0 := eq790940 X0 X1
       grind)
    | exact resolve eq790940 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq790940
  have eq794043 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq791438 X1 (σ X0)
       grind)
    | exact superpose eq791438 eq15
    | (have j1 := eq791438 X1 (σ X0)
       grind)
    | exact resolve eq15 eq791438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791438
  have eq794929 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq794043 X0 X1
       have i₂ := eq131878 X0
       grind)
    | exact superpose eq131878 eq794043
    | (have j0 := eq794043 X0 X1
       grind)
    | exact resolve eq794043 eq131878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131878 eq794043
  have eq798883 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq794929 x y
       grind)
    | exact superpose eq794929 eq16
    | (have j1 := eq794929 x y
       grind)
    | exact resolve eq16 eq794929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794929
  have eq802486 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq798883
       have i₂ := eq785411 x y
       grind)
    | exact superpose eq785411 eq798883
    | (have j1 := eq785411 y y
       grind)
    | (have r₁ := eq798883
       have r₂ := eq785411 x y
       grind)
    | exact resolve eq798883 eq785411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785411 eq798883
  have eq802489 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq802486
  have eq802490 : (σ y) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq802489
  have eq802692 : (M.op x x) = (τ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq802490
       grind)
    | exact superpose eq802490 eq10
    | exact resolve eq10 eq802490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802490
  have eq803186 : y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq802692
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq802692
    | exact resolve eq802692 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802692
  have eq803187 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq803186
  have eq806178 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq803187
       grind)
    | exact superpose eq803187 eq9
    | exact resolve eq9 eq803187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq806205 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq106 y y x
       have i₂ := eq803187
       grind)
    | exact superpose eq803187 eq106
    | exact resolve eq106 eq803187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803187
  have eq806361 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq806205 X0
       have i₂ := eq91 y X0
       grind)
    | exact superpose eq91 eq806205
    | exact resolve eq806205 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806205
  have eq808412 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq806178 X0
       have i₂ := eq806361 X0
       grind)
    | exact superpose eq806361 eq806178
    | exact resolve eq806178 eq806361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806178 eq806361
  have eq808728 : ∀ X0 : G, y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq808412 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808412
  have eq809129 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq133017 x
       have i₂ := eq808728 X0
       grind)
    | exact superpose eq808728 eq133017
    | (have j1 := eq808728 X0
       grind)
    | exact resolve eq133017 eq808728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133017
  have eq809447 : ∀ X0 : G, y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq91 x x
       have i₂ := eq808728 X0
       grind)
    | exact superpose eq808728 eq91
    | (have j1 := eq808728 X0
       grind)
    | exact resolve eq91 eq808728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq808728
  have eq811732 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq809129 X0
       grind)
    | exact superpose eq809129 eq16
    | (have j1 := eq809129 X0
       grind)
    | exact resolve eq16 eq809129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809129
  have eq811979 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (M.op y X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq811732 X0
       have i₂ := eq809447 X1
       grind)
    | exact superpose eq809447 eq811732
    | (have j0 := eq811732 X0
       have j1 := eq809447 X0
       grind)
    | exact resolve eq811732 eq809447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809447 eq811732
  have eq811980 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq811979 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811979
  have eq812801 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq811980 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811980
  have eq812802 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq812801 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812801
  have eq812937 : ∀ X0 : G, (M.op (M.op (M.op (τ y) X0) (τ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq132331 y X0
       have i₂ := eq812802 y
       grind)
    | exact superpose eq812802 eq132331
    | exact resolve eq132331 eq812802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132331
  have eq813268 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq106 y X1 X0
       have i₂ := eq812802 X0
       grind)
    | exact superpose eq812802 eq106
    | exact resolve eq106 eq812802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq813385 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq78 y X0
       have i₂ := eq812802 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq812802 eq78
    | exact resolve eq78 eq812802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq813820 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq813385 X0
       have i₂ := eq812802 y
       grind)
    | exact superpose eq812802 eq813385
    | exact resolve eq813385 eq812802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813385
  have eq813902 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq813268 X0 X0
       have i₂ := eq812802 X0
       grind)
    | exact superpose eq812802 eq813268
    | exact resolve eq813268 eq812802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813268
  have eq814232 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq813820 X0
       have i₂ := eq812802 X0
       grind)
    | exact superpose eq812802 eq813820
    | exact resolve eq813820 eq812802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812802 eq813820
  have eq828471 : ∀ X0 : G, (M.op (τ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq812937 X0
       have i₂ := eq813902 X0 (τ y)
       grind)
    | exact superpose eq813902 eq812937
    | exact resolve eq812937 eq813902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812937
  have eq829207 : ∀ X0 : G, (M.op (M.op (M.op (σ (σ (τ y))) X0) (σ (σ (τ y)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq136413 (τ y) X0
       have i₂ := eq828471 (τ y)
       grind)
    | exact superpose eq828471 eq136413
    | exact resolve eq136413 eq828471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136413 eq828471
  have eq829982 : ∀ X0 : G, (M.op (σ (σ (τ y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq829207 X0
       have i₂ := eq813902 X0 (σ (σ (τ y)))
       grind)
    | exact superpose eq813902 eq829207
    | exact resolve eq829207 eq813902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829207
  have eq830142 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq829982 X0
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq829982
    | exact resolve eq829982 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829982
  have eq831077 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq813902 X0 (σ y)
       have i₂ := eq830142 X0
       grind)
    | exact superpose eq830142 eq813902
    | exact resolve eq813902 eq830142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813902 eq830142
  have eq837060 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq831077 (σ x)
       grind)
    | exact superpose eq831077 eq16
    | exact resolve eq16 eq831077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831077
  have eq837509 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq837060
       have i₂ := eq814232 x
       grind)
    | exact superpose eq814232 eq837060
    | exact resolve eq837060 eq814232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814232 eq837060
  have eq837510 : False := by grind
  exact eq837510

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else if m(Y,Y) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_pyy_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq69 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = (M.op (τ X1) X0) := by
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
  have eq77 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 (M.op X0 X0) X0 X2
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq24
    | exact resolve eq24 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq85 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq9
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq9
    | exact resolve eq9 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq85
    | exact resolve eq85 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq181 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq179 (σ X0)
       grind)
    | exact superpose eq179 eq23
    | exact resolve eq23 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 y x
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 y x
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq82
    | exact resolve eq82 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq605 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq181 X0
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq181
    | (have j1 := eq65 X0 X0
       grind)
    | exact resolve eq181 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq181
  have eq623 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq605 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq636 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq623 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq623
    | (have j0 := eq623 X0
       grind)
    | exact resolve eq623 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq1375 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq636 (τ X0)
       grind)
    | exact superpose eq636 eq19
    | (have j1 := eq636 (τ X0)
       grind)
    | exact resolve eq19 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq636
  have eq1377 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1375 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1375
    | (have j0 := eq1375 X0
       grind)
    | exact resolve eq1375 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1375
  have eq1393 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1377 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1377
    | (have j0 := eq1377 X0
       grind)
    | exact resolve eq1377 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq1408 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1393 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1393
    | (have j0 := eq1393 X0
       grind)
    | exact resolve eq1393 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1952 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq69
    | exact resolve eq69 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq2026 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1952 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1952
    | (have j0 := eq1952 X0 X1
       grind)
    | exact resolve eq1952 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952
  have eq3876 : ∀ X0 X1 X2 : G, (k (k X1 X0) (τ X2)) = (τ (k (σ (M.op X0 X1)) X2)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (k X1 X0) X2
       have i₂ := eq2026 X1 X0
       grind)
    | exact superpose eq2026 eq31
    | (have j1 := eq2026 X1 X0
       grind)
    | exact resolve eq31 eq2026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2026
  have eq3883 : ∀ X0 X1 X2 : G, (k (k X1 X0) (τ X2)) = (k (M.op X0 X1) (τ X2)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3876 X0 X1 X2
       have i₂ := eq31 (M.op X0 X1) X2
       grind)
    | exact superpose eq31 eq3876
    | (have j0 := eq3876 X0 X1 X2
       grind)
    | exact resolve eq3876 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3876
  have eq4825 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq449
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq449
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq449 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq4828 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq4825
  have eq93576 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1408 (τ X0)
       have i₂ := eq3883 (τ X0) (τ X0) X0
       grind)
    | exact superpose eq3883 eq1408
    | (have j0 := eq1408 (τ X0)
       have j1 := eq3883 (τ X0) (τ X0) x
       grind)
    | exact resolve eq1408 eq3883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408 eq3883
  have eq93955 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq93576 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93576
  have eq94165 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq93955 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq93955
    | (have j0 := eq93955 X0
       grind)
    | exact resolve eq93955 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93955
  have eq94416 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq94165 X0
       have i₂ := eq179 (τ X0)
       grind)
    | exact superpose eq179 eq94165
    | (have j0 := eq94165 X0
       grind)
    | exact resolve eq94165 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq94165
  have eq94773 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq94416 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94416
    | exact resolve eq94416 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94416
  have eq95088 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq94773 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq94773
    | (have j0 := eq94773 X0
       grind)
    | exact resolve eq94773 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq94773
  have eq95115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq95088 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95088
    | (have j0 := eq95088 X0
       grind)
    | exact resolve eq95088 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95088
  have eq95123 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq95115 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq95115 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq95115 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95115
  have eq95416 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq95123 (σ X0)
       grind)
    | exact superpose eq95123 eq15
    | exact resolve eq15 eq95123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95429 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq95123 (τ X0)
       grind)
    | exact superpose eq95123 eq34
    | exact resolve eq34 eq95123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq95535 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95429 X0
       have i₂ := eq95123 X0
       grind)
    | exact superpose eq95123 eq95429
    | exact resolve eq95429 eq95123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95429
  have eq95548 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95416 X0
       have i₂ := eq95123 X0
       grind)
    | exact superpose eq95123 eq95416
    | exact resolve eq95416 eq95123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95123 eq95416
  have eq95965 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85 (τ X0) X1
       have i₂ := eq95535 X0
       grind)
    | exact superpose eq95535 eq85
    | exact resolve eq85 eq95535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95535
  have eq96403 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq77 (σ X0)
       have i₂ := eq95548 X0
       grind)
    | exact superpose eq95548 eq77
    | exact resolve eq77 eq95548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq96449 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq95548 X0
       grind)
    | exact superpose eq95548 eq9
    | exact resolve eq9 eq95548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96450 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq95548 X0
       grind)
    | exact superpose eq95548 eq9
    | exact resolve eq9 eq95548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96476 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq99 (σ X0) (σ X0)
       have i₂ := eq95548 X0
       grind)
    | exact superpose eq95548 eq99
    | exact resolve eq99 eq95548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99663 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (σ X0)) X1) (σ (σ (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq96450 (σ X0) X1
       have i₂ := eq95548 X0
       grind)
    | exact superpose eq95548 eq96450
    | exact resolve eq96450 eq95548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96450
  have eq103083 : (σ y) = (M.op (M.op (σ (M.op y y)) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq96449 y (σ x)
       have i₂ := eq4828
       grind)
    | exact superpose eq4828 eq96449
    | exact resolve eq96449 eq4828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4828 eq96449
  have eq103393 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq103083
       have i₂ := eq96403 y
       grind)
    | exact superpose eq96403 eq103083
    | exact resolve eq103083 eq96403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96403 eq103083
  have eq103464 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq103393
       have i₂ := eq95548 y
       grind)
    | exact superpose eq95548 eq103393
    | exact resolve eq103393 eq95548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103393
  have eq103492 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq103464
       have i₂ := eq95548 x
       grind)
    | exact superpose eq95548 eq103464
    | exact resolve eq103464 eq95548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95548 eq103464
  have eq473344 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq103492
       grind)
    | exact superpose eq103492 eq10
    | exact resolve eq10 eq103492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103492
  have eq473581 : (σ y) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq473344
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq473344
    | exact resolve eq473344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473344
  have eq473736 : (M.op x x) = (τ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq473581
       grind)
    | exact superpose eq473581 eq10
    | exact resolve eq10 eq473581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473581
  have eq473971 : y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq473736
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq473736
    | exact resolve eq473736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473736
  have eq473972 : y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq473971
  have eq473989 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq85 y X0
       have i₂ := eq473972
       grind)
    | exact superpose eq473972 eq85
    | exact resolve eq85 eq473972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474342 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq554 y y x
       have i₂ := eq473972
       grind)
    | exact superpose eq473972 eq554
    | exact resolve eq554 eq473972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473972
  have eq474766 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq474342 X0
       have i₂ := eq99 y X0
       grind)
    | exact superpose eq99 eq474342
    | exact resolve eq474342 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474342
  have eq476484 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq473989 X0
       have i₂ := eq474766 X0
       grind)
    | exact superpose eq474766 eq473989
    | exact resolve eq473989 eq474766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473989 eq474766
  have eq477050 : ∀ X0 : G, y = (M.op y x) ∨ y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq476484 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476484
  have eq477133 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq99 y x
       have i₂ := eq477050 X0
       grind)
    | exact superpose eq477050 eq99
    | (have j1 := eq477050 y
       grind)
    | exact resolve eq99 eq477050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477050
  have eq477459 : y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq477133 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477133
  have eq477637 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq85 y X0
       have i₂ := eq477459
       grind)
    | exact superpose eq477459 eq85
    | exact resolve eq85 eq477459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq477990 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq554 y y x
       have i₂ := eq477459
       grind)
    | exact superpose eq477459 eq554
    | exact resolve eq554 eq477459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477459
  have eq478416 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq477990 X0
       have i₂ := eq99 y X0
       grind)
    | exact superpose eq99 eq477990
    | exact resolve eq477990 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477990
  have eq480139 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq477637 X0
       have i₂ := eq478416 X0
       grind)
    | exact superpose eq478416 eq477637
    | exact resolve eq477637 eq478416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477637 eq478416
  have eq480707 : ∀ X0 : G, y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq480139 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480139
  have eq480899 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq96476 x
       have i₂ := eq480707 X0
       grind)
    | exact superpose eq480707 eq96476
    | (have j1 := eq480707 X0
       grind)
    | exact resolve eq96476 eq480707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96476
  have eq481115 : ∀ X0 : G, y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq99 x x
       have i₂ := eq480707 X0
       grind)
    | exact superpose eq480707 eq99
    | (have j1 := eq480707 X0
       grind)
    | exact resolve eq99 eq480707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq480707
  have eq485693 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq480899 X0
       grind)
    | exact superpose eq480899 eq16
    | (have j1 := eq480899 X0
       grind)
    | exact resolve eq16 eq480899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480899
  have eq486170 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (M.op y X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq485693 X0
       have i₂ := eq481115 X1
       grind)
    | exact superpose eq481115 eq485693
    | (have j0 := eq485693 X0
       have j1 := eq481115 X0
       grind)
    | exact resolve eq485693 eq481115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481115 eq485693
  have eq486171 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq486170 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486170
  have eq486172 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq486171 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486171
  have eq486234 : ∀ X0 : G, (M.op (M.op (M.op (τ y) X0) (τ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq95965 y X0
       have i₂ := eq486172 y
       grind)
    | exact superpose eq486172 eq95965
    | exact resolve eq95965 eq486172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95965
  have eq486539 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq554 y X1 X0
       have i₂ := eq486172 X0
       grind)
    | exact superpose eq486172 eq554
    | exact resolve eq554 eq486172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq486848 : ∀ X0 : G, y = (M.op (M.op (M.op y y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq86 y X0
       have i₂ := eq486172 (M.op (M.op y y) X0)
       grind)
    | exact superpose eq486172 eq86
    | exact resolve eq86 eq486172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq487664 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq486848 X0
       have i₂ := eq486172 y
       grind)
    | exact superpose eq486172 eq486848
    | exact resolve eq486848 eq486172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486848
  have eq487931 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq486539 X0 X0
       have i₂ := eq486172 X0
       grind)
    | exact superpose eq486172 eq486539
    | exact resolve eq486539 eq486172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486539
  have eq488266 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq487664 X0
       have i₂ := eq486172 X0
       grind)
    | exact superpose eq486172 eq487664
    | exact resolve eq487664 eq486172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486172 eq487664
  have eq528996 : ∀ X0 : G, (M.op (τ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq486234 X0
       have i₂ := eq487931 X0 (τ y)
       grind)
    | exact superpose eq487931 eq486234
    | exact resolve eq486234 eq487931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486234
  have eq531110 : ∀ X0 : G, (M.op (M.op (M.op (σ (σ (τ y))) X0) (σ (σ (τ y)))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq99663 (τ y) X0
       have i₂ := eq528996 (τ y)
       grind)
    | exact superpose eq528996 eq99663
    | exact resolve eq99663 eq528996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99663 eq528996
  have eq532645 : ∀ X0 : G, (M.op (σ (σ (τ y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq531110 X0
       have i₂ := eq487931 X0 (σ (σ (τ y)))
       grind)
    | exact superpose eq487931 eq531110
    | exact resolve eq531110 eq487931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531110
  have eq532960 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq532645 X0
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq532645
    | exact resolve eq532645 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532645
  have eq534109 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq487931 X0 (σ y)
       have i₂ := eq532960 X0
       grind)
    | exact superpose eq532960 eq487931
    | exact resolve eq487931 eq532960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487931 eq532960
  have eq554201 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq534109 (σ x)
       grind)
    | exact superpose eq534109 eq16
    | exact resolve eq16 eq534109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534109
  have eq554605 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq554201
       have i₂ := eq488266 x
       grind)
    | exact superpose eq488266 eq554201
    | exact resolve eq554201 eq488266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488266 eq554201
  have eq554606 : False := by grind
  exact eq554606

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq45 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq31
    | exact resolve eq31 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq59 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op (τ X1) X0) = X0 := by
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
  have eq78 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  clear eq20
  have eq88 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq12
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq78 X0
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq9
    | exact resolve eq9 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq9
    | exact resolve eq9 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq88 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq126 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq89
    | exact resolve eq89 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq148 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq126 X0 X1
       grind)
    | exact superpose eq126 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X1)
       have r₂ := eq126 X0 X1
       grind)
    | exact resolve eq12 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq148 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq198 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq91 (τ X0)
       grind)
    | exact superpose eq91 eq19
    | exact resolve eq19 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq198 X0
       have i₂ := eq126 (τ X0) (τ X0)
       grind)
    | exact superpose eq126 eq198
    | exact resolve eq198 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq202 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq57
    | exact resolve eq57 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq250 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) X1))) = (σ (M.op (M.op (τ X0) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) X1)
       have i₂ := eq157 (τ X0) X1
       grind)
    | exact superpose eq157 eq18
    | exact resolve eq18 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1345 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq199 x
       have i₂ := eq59 (τ x) x
       grind)
    | exact superpose eq59 eq199
    | (have j1 := eq59 (τ X0) X0
       grind)
    | exact resolve eq199 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq1358 : ∀ X0 X1 X2 : G, (τ (k (k X0 (σ X1)) X2)) = (k (M.op X1 (τ X0)) (τ X2)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (M.op X1 (τ X0)) X2
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq31
    | (have j1 := eq59 X1 X0
       grind)
    | exact resolve eq31 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq59
  have eq1365 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1345 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345
  have eq1366 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (k (M.op X1 (τ X0)) (τ X2)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1358 X0 X1 X2
       have i₂ := eq45 X0 X1 X2
       grind)
    | exact superpose eq45 eq1358
    | (have j0 := eq1358 X0 X1 X2
       grind)
    | exact resolve eq1358 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1358
  have eq1371 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1365 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1365
    | (have j0 := eq1365 X0
       grind)
    | exact resolve eq1365 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq3895 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 (M.op (M.op (τ X0) (τ X0)) X1)
       have i₂ := eq90 (τ X0) X1
       grind)
    | exact superpose eq90 eq250
    | exact resolve eq250 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq3951 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3895 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3895
    | exact resolve eq3895 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3895
  have eq7863 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (k (σ X0) (σ X0)) X0
       have i₂ := eq1371 (σ X0)
       grind)
    | exact superpose eq1371 eq25
    | (have j1 := eq1371 (σ X0)
       grind)
    | exact resolve eq25 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq7872 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7863 x
       have i₂ := eq25 (σ x) x
       grind)
    | exact superpose eq25 eq7863
    | (have j0 := eq7863 X0
       grind)
    | exact resolve eq7863 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7863
  have eq7888 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7872 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7872
    | (have j0 := eq7872 X0
       grind)
    | exact resolve eq7872 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7872
  have eq7902 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7888 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7888
    | (have j0 := eq7888 X0
       grind)
    | exact resolve eq7888 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7888
  have eq45668 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7902 (τ X0)
       have i₂ := eq1366 X0 (τ X0) X0
       grind)
    | exact superpose eq1366 eq7902
    | (have j0 := eq7902 (τ X0)
       have j1 := eq1366 X0 (τ X0) x
       grind)
    | exact resolve eq7902 eq1366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366 eq7902
  have eq45703 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq45668 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45668
  have eq45747 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq45703 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq45703
    | (have j0 := eq45703 X0
       grind)
    | exact resolve eq45703 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45703
  have eq45806 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (τ X0))) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq45747 X0
       have i₂ := eq91 (τ X0)
       grind)
    | exact superpose eq91 eq45747
    | (have j0 := eq45747 X0
       grind)
    | exact resolve eq45747 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq45747
  have eq45832 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45806 X0
       have i₂ := eq126 (τ X0) (τ X0)
       grind)
    | exact superpose eq126 eq45806
    | (have j0 := eq45806 X0
       grind)
    | exact resolve eq45806 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq45806
  have eq52145 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq45832 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45832
    | exact resolve eq45832 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52259 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq157 (τ X0) (τ X0)
       have i₂ := eq45832 X0
       grind)
    | exact superpose eq45832 eq157
    | (have j1 := eq45832 X0
       grind)
    | exact resolve eq157 eq45832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45832
  have eq52334 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq52259 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq52259
    | (have j0 := eq52259 X0
       grind)
    | exact resolve eq52259 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq52259
  have eq52335 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq52334 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52334
  have eq52392 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52145 X0
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq52145
    | (have j0 := eq52145 X0
       grind)
    | exact resolve eq52145 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq52145
  have eq52399 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52392 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq52392
    | (have j0 := eq52392 X0
       grind)
    | exact resolve eq52392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52392
  have eq52405 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq52399 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq52399 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq52399 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52399
  have eq52588 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq52405 (σ X0)
       grind)
    | exact superpose eq52405 eq15
    | exact resolve eq15 eq52405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52652 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq52588 X0
       have i₂ := eq52405 X0
       grind)
    | exact superpose eq52405 eq52588
    | exact resolve eq52588 eq52405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52588
  have eq52956 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) (M.op (τ (k X0 X0)) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3951 X0 X1
       have i₂ := eq52335 X0
       grind)
    | exact superpose eq52335 eq3951
    | exact resolve eq3951 eq52335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3951
  have eq52983 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) (M.op (τ (k X0 X0)) X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (τ X0) X1
       have i₂ := eq52335 X0
       grind)
    | exact superpose eq52335 eq90
    | exact resolve eq90 eq52335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq53227 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) (M.op (τ (M.op X0 X0)) X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52983 X0 X1
       have i₂ := eq52405 X0
       grind)
    | exact superpose eq52405 eq52983
    | exact resolve eq52983 eq52405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52983
  have eq53252 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) (M.op (τ (M.op X0 X0)) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52956 X0 X1
       have i₂ := eq52405 X0
       grind)
    | exact superpose eq52405 eq52956
    | exact resolve eq52956 eq52405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52956
  have eq53565 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq78 (σ X0)
       have i₂ := eq52652 X0
       grind)
    | exact superpose eq52652 eq78
    | exact resolve eq78 eq52652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60543 : ∀ X0 X1 X2 : G, (M.op (σ X2) X0) = X0 ∨ (M.op (σ X2) (σ X2)) = X0 ∨ (M.op X0 (σ X2)) = (σ (k X2 (k (τ X0) (M.op (τ X0) (M.op (τ (M.op X0 X0)) X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq202 X0 (M.op (τ X0) (M.op (τ (M.op X0 X0)) X1)) X2
       have i₂ := eq53252 X0 X1
       grind)
    | exact superpose eq53252 eq202
    | exact resolve eq202 eq53252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq53252
  have eq60635 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = X0 ∨ (M.op (σ X2) X0) = X0 ∨ (M.op X0 (σ X2)) = (σ (k X2 (k (τ X0) (M.op (τ X0) (M.op (τ (M.op X0 X0)) X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60543 X0 X1 X2
       have i₂ := eq52652 X2
       grind)
    | exact superpose eq52652 eq60543
    | (have j0 := eq60543 X0 X1 X2
       grind)
    | exact resolve eq60543 eq52652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52652 eq60543
  have eq60743 : ∀ X0 X1 X2 : G, (M.op X0 (σ X2)) = (σ (k X2 (M.op (M.op (τ X0) (M.op (τ (M.op X0 X0)) X1)) (τ X0)))) ∨ (σ (M.op X2 X2)) = X0 ∨ (M.op (σ X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60635 X0 X1 X2
       have i₂ := eq157 (τ X0) (M.op (τ (M.op X0 X0)) X1)
       grind)
    | exact superpose eq157 eq60635
    | (have j0 := eq60635 X0 X1 X2
       grind)
    | exact resolve eq60635 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq60635
  have eq60830 : ∀ X0 X2 : G, (M.op X0 (σ X2)) = (σ (k X2 (τ X0))) ∨ (σ (M.op X2 X2)) = X0 ∨ (M.op (σ X2) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq60743 X0 x X2
       have i₂ := eq53227 X0 x
       grind)
    | exact superpose eq53227 eq60743
    | (have j0 := eq60743 X0 x X2
       grind)
    | exact resolve eq60743 eq53227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53227 eq60743
  have eq60885 : ∀ X0 X2 : G, (M.op X0 (σ X2)) = (k (σ X2) X0) ∨ (σ (M.op X2 X2)) = X0 ∨ (M.op (σ X2) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq60830 X0 X2
       have i₂ := eq19 X0 X2
       grind)
    | exact superpose eq19 eq60830
    | (have j0 := eq60830 X0 X2
       grind)
    | exact resolve eq60830 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60830
  have eq60919 : ∀ X0 X2 : G, (M.op X0 (σ X2)) = (k (σ X2) X0) ∨ (σ (M.op X2 X2)) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq60885 X0 X2
       have j1 := eq12 (σ X2) X0
       grind)
    | (have r₁ := eq60885 (M.op X0 (σ (M.op X2 X2))) X2
       have r₂ := eq12 X0 (σ (M.op X2 X2))
       grind)
    | (have r₁ := eq60885 x X2
       have r₂ := eq12 (σ X2) x
       grind)
    | exact resolve eq60885 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60885
  have eq69081 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60919 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60919
    | (have j0 := eq60919 X1 (τ X0)
       grind)
    | exact resolve eq60919 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69202 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq60919 (σ X0) X1
       grind)
    | exact superpose eq60919 eq15
    | (have j1 := eq60919 (σ X0) X1
       grind)
    | exact resolve eq15 eq60919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60919
  have eq69673 : ∀ X0 X1 : G, (σ (τ (k X0 X0))) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69081 X0 X1
       have i₂ := eq52335 X0
       grind)
    | exact superpose eq52335 eq69081
    | (have j0 := eq69081 X0 X1
       grind)
    | exact resolve eq69081 eq52335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52335 eq69081
  have eq69833 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69673 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq69673
    | (have j0 := eq69673 X0 X1
       grind)
    | exact resolve eq69673 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69673
  have eq69909 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69833 X0 X1
       have i₂ := eq52405 X0
       grind)
    | exact superpose eq52405 eq69833
    | (have j0 := eq69833 X0 X1
       grind)
    | exact resolve eq69833 eq52405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52405 eq69833
  have eq70280 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq69909 X1 (τ X0)
       grind)
    | exact superpose eq69909 eq19
    | (have j1 := eq69909 X1 (τ X0)
       grind)
    | exact resolve eq19 eq69909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq69909
  have eq80415 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq70280 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70280
    | exact resolve eq70280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70280
  have eq80770 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq80415 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq80415
    | (have j0 := eq80415 X0 X1
       grind)
    | exact resolve eq80415 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80415
  have eq103169 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69202 x y
       grind)
    | exact superpose eq69202 eq16
    | (have j1 := eq69202 x y
       grind)
    | exact resolve eq16 eq69202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69202
  have eq103893 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq103169
       have i₂ := eq80770 x y
       grind)
    | exact superpose eq80770 eq103169
    | (have j1 := eq80770 x y
       grind)
    | (have r₁ := eq103169
       have r₂ := eq80770 x y
       grind)
    | exact resolve eq103169 eq80770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80770 eq103169
  have eq103896 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq103893
  have eq104675 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq103896
       grind)
    | exact superpose eq103896 eq10
    | exact resolve eq10 eq103896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103896
  have eq104883 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq104675
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq104675
    | exact resolve eq104675 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104675
  have eq104884 : x = (M.op y y) := by grind
  clear eq104883
  have eq104900 : y = (M.op x y) := by
    first
    | (have i₁ := eq78 y
       have i₂ := eq104884
       grind)
    | exact superpose eq104884 eq78
    | exact resolve eq78 eq104884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq104943 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53565 y
       have i₂ := eq104884
       grind)
    | exact superpose eq104884 eq53565
    | exact resolve eq53565 eq104884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53565 eq104884
  have eq111273 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq104943
       grind)
    | exact superpose eq104943 eq16
    | exact resolve eq16 eq104943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104943
  have eq111488 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq111273
       have i₂ := eq104900
       grind)
    | exact superpose eq104900 eq111273
    | exact resolve eq111273 eq104900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104900 eq111273
  have eq111489 : False := by grind
  exact eq111489

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
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
  have eq44 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq44
    | (have j0 := eq44 (σ X0) (σ X1)
       grind)
    | exact resolve eq44 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq44 X1 (τ X0)
       grind)
    | exact superpose eq44 eq19
    | (have j1 := eq44 X1 (τ X0)
       grind)
    | exact resolve eq19 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq85 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq111 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (M.op X0 X1) X0 X1 (M.op (M.op X0 (M.op X0 X1)) X2)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 (M.op X0 X1)) X2
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq139 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57 y x
       grind)
    | exact superpose eq57 eq16
    | (have j1 := eq57 y x
       grind)
    | exact resolve eq16 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq317 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61
    | exact resolve eq61 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq341 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq317 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq317
    | (have j0 := eq317 X0 X1
       grind)
    | exact resolve eq317 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq421 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq139
       have i₂ := eq44 y x
       grind)
    | exact superpose eq44 eq139
    | (have j1 := eq44 (σ y) (σ x)
       grind)
    | exact resolve eq139 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq424 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq421
  have eq427 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq85 y
       have i₂ := eq424
       grind)
    | exact superpose eq424 eq85
    | exact resolve eq85 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 : G, y = (M.op (M.op x (M.op y X0)) y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq424
       grind)
    | exact superpose eq424 eq9
    | exact resolve eq9 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 : G, (M.op (M.op (M.op x X0) y) X0) = X0 ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq427
       grind)
    | exact superpose eq427 eq9
    | exact resolve eq9 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq3115 : y = (M.op (M.op x x) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq429 y
       have i₂ := eq424
       grind)
    | exact superpose eq424 eq429
    | exact resolve eq429 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424 eq429
  have eq3160 : y = (M.op (M.op x x) y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq3115
  have eq3676 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq540 x
       have i₂ := eq3160
       grind)
    | exact superpose eq3160 eq540
    | exact resolve eq540 eq3160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq3160
  have eq3724 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq3676
  have eq3872 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3724
       grind)
    | exact superpose eq3724 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3724
       grind)
    | exact resolve eq12 eq3724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3724
  have eq3913 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq3872
  have eq3978 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq139
       have i₂ := eq3913
       grind)
    | exact superpose eq3913 eq139
    | exact resolve eq139 eq3913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq3913
  have eq3998 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq3978
  have eq3999 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq3998
  have eq4074 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85 (σ y)
       have i₂ := eq3999
       grind)
    | exact superpose eq3999 eq85
    | exact resolve eq85 eq3999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4080 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq3999
       grind)
    | exact superpose eq3999 eq9
    | exact resolve eq9 eq3999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4232 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4074
       grind)
    | exact superpose eq4074 eq16
    | exact resolve eq16 eq4074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4905 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ y) X0) (σ x)) X0) X1) = (M.op X0 (M.op (M.op (M.op (M.op (σ y) X0) (σ x)) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq111 (M.op (M.op (σ y) X0) (σ x)) X0 x
       have i₂ := eq4080 X0
       grind)
    | exact superpose eq4080 eq111
    | exact resolve eq111 eq4080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq4923 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4905 X0 X1
       have i₂ := eq4080 X0
       grind)
    | exact superpose eq4080 eq4905
    | exact resolve eq4905 eq4080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4080 eq4905
  have eq5067 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4923 (σ y) (σ y)
       have i₂ := eq3999
       grind)
    | exact superpose eq3999 eq4923
    | exact resolve eq4923 eq3999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3999 eq4923
  have eq5273 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq5067
       grind)
    | exact superpose eq5067 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq5067
       grind)
    | exact resolve eq12 eq5067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5067
  have eq5315 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq5273
  have eq5321 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq5315
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5315
    | exact resolve eq5315 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5315
  have eq5326 : (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq5321
       have i₂ := eq4074
       grind)
    | exact superpose eq4074 eq5321
    | exact resolve eq5321 eq4074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4074 eq5321
  have eq5768 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq341 x y
       have i₂ := eq5326
       grind)
    | exact superpose eq5326 eq341
    | (have j0 := eq341 x y
       grind)
    | exact resolve eq341 eq5326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq5326
  have eq5818 : x = (M.op y y) := by
    first
    | (have r₁ := eq5768
       have r₂ := eq4232
       grind)
    | exact resolve eq5768 eq4232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5768
  have eq6027 : y = (M.op x y) := by
    first
    | (have i₁ := eq85 y
       have i₂ := eq5818
       grind)
    | exact superpose eq5818 eq85
    | exact resolve eq85 eq5818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq5818
  have eq6588 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4232
       have i₂ := eq6027
       grind)
    | exact superpose eq6027 eq4232
    | exact resolve eq4232 eq6027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4232 eq6027
  have eq6644 : False := by grind
  exact eq6644

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  clear eq36
  have eq78 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq78 y x
       grind)
    | exact superpose eq78 eq75
    | (have j1 := eq78 y x
       grind)
    | exact resolve eq75 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq112 eq78
    | (have j0 := eq78 (σ y) (σ x)
       grind)
    | exact resolve eq78 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq563
    | exact resolve eq563 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq567 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq564
       have r₂ := eq27
       grind)
    | exact resolve eq564 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq571 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq567 eq14
    | exact resolve eq14 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq731 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq567 eq571
    | exact resolve eq571 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq741 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq731
  have eq819 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq571 sF3
       have i₂ := eq597 sF3
       grind)
    | exact superpose eq597 eq571
    | exact resolve eq571 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq830 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq819 eq741
    | exact resolve eq741 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq819
  have eq846 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq830
  have eq857 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq846 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq846
       grind)
    | exact resolve eq13 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq866 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq857
  have eq871 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq866
    | exact resolve eq866 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq909 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq871 eq112
    | exact resolve eq112 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq871
  have eq912 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq909
  have eq916 : y = (M.op y x) := by
    first
    | (have r₁ := eq912
       have r₂ := eq27
       grind)
    | exact resolve eq912 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq920 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq916
       grind)
    | exact superpose eq916 eq14
    | exact resolve eq14 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq921 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq916
       grind)
    | exact superpose eq916 eq14
    | exact resolve eq14 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq968 : x = (M.op (M.op y y) x) := by
    first
    | (have i₁ := eq920 x
       have i₂ := eq916
       grind)
    | exact superpose eq916 eq920
    | exact resolve eq920 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq996 : y = (M.op y y) := by
    first
    | (have i₁ := eq921 y
       have i₂ := eq597 y
       grind)
    | exact superpose eq597 eq921
    | exact resolve eq921 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq921
  have eq1022 : x = (M.op y x) := by
    first
    | (have i₁ := eq968
       have i₂ := eq996
       grind)
    | exact superpose eq996 eq968
    | exact resolve eq968 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq1025 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq996
       grind)
    | exact superpose eq996 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq996
       grind)
    | exact resolve eq13 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1035 : y = (k y y) := by grind
  clear eq1025
  have eq1036 : x = y := by
    first
    | (have i₁ := eq1022
       have i₂ := eq916
       grind)
    | exact superpose eq916 eq1022
    | exact resolve eq1022 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1037 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1036
       grind)
    | exact superpose eq1036 eq18
    | exact resolve eq18 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1038 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1036
       grind)
    | exact superpose eq1036 eq24
    | exact resolve eq24 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1058 : x = (M.op x x) := by
    first
    | (have i₁ := eq916
       have i₂ := eq1036
       grind)
    | exact superpose eq1036 eq916
    | exact resolve eq916 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq1075 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1038
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1038
    | exact resolve eq1038 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1076 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1075 eq26
    | exact resolve eq26 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1075
  have eq1123 : x = (k x x) := by
    first
    | (have i₁ := eq1035
       have i₂ := eq1036
       grind)
    | exact superpose eq1036 eq1035
    | exact resolve eq1035 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035 eq1036
  have eq1125 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1123
       grind)
    | exact superpose eq1123 eq43
    | exact resolve eq43 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1123
  have eq1129 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1125
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1125
    | exact resolve eq1125 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1167 : x = (M.op x y) := by
    first
    | (have i₁ := eq1058
       have i₂ := eq1037
       grind)
    | exact superpose eq1037 eq1058
    | exact resolve eq1058 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037 eq1058
  have eq1168 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1167 eq20
    | exact resolve eq20 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1167
  have eq1200 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1168
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1168
    | exact resolve eq1168 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1168
  have eq1263 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1200 eq1129
    | exact resolve eq1129 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1266 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1263 eq78
    | (have j0 := eq78 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq78 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1263
  have eq1267 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1266
  have eq1273 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1200 eq1076
    | exact resolve eq1076 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076 eq1200
  have eq1302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1267 eq1273
    | exact resolve eq1273 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267 eq1273
  have eq1303 : False := by grind
  exact eq1303
