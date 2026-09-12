import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyy_pyx_pxy_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq76 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op (M.op X1 X2) X0) X1) (M.op (M.op (M.op X1 X2) X0) X1)) = X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) (M.op (M.op (M.op X1 X2) X0) X1)) = X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq76 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq109 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq110 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq119 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq109
       grind)
    | exact superpose eq109 eq16
    | exact resolve eq16 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq121 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq110
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq127 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq121
  have eq673 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (k X0 X1)) X2) (σ X0)) X2) = X2 ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (σ X0) (σ X1)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq14
    | (have j1 := eq62 X0 X1
       grind)
    | exact resolve eq14 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq845 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    grind
  clear eq89
  have eq852 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq845 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq920 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq57 X1 X2 X0
       grind)
    | exact superpose eq57 eq51
    | exact resolve eq51 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq961 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op X0 X1) (M.op X0 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq852 X1 (M.op X0 X2) X0
       have i₂ := eq51 X0 X2
       grind)
    | exact superpose eq51 eq852
    | exact resolve eq852 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1000 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq61 eq852
    | exact resolve eq852 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1003 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq852 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq852
    | exact resolve eq852 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq19275 : (M.op y y) = (τ (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq127
       grind)
    | exact superpose eq127 eq16
    | exact resolve eq16 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq19332 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq126 eq19275
    | exact resolve eq19275 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq19275
  have eq31590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq31597 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq31590
    | exact resolve eq31590 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31590
  have eq31608 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq31597
       have r₂ := eq28
       grind)
    | exact resolve eq31597 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31597
  have eq31625 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31608 eq55
    | exact resolve eq55 eq31608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31608
  have eq31679 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq31625
  have eq31693 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31679 eq51
    | exact resolve eq51 eq31679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31679
  have eq31750 : x = (M.op y y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq31693
    | exact resolve eq31693 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31693
  have eq31764 : x = (M.op y x) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55 y y
       have i₂ := eq31750
       grind)
    | exact superpose eq31750 eq55
    | exact resolve eq55 eq31750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31750
  have eq31818 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31764
  have eq32132 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51 y x
       have i₂ := eq31818
       grind)
    | exact superpose eq31818 eq51
    | exact resolve eq51 eq31818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32179 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1003 y x
       have i₂ := eq31818
       grind)
    | exact superpose eq31818 eq1003
    | exact resolve eq1003 eq31818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003 eq31818
  have eq32189 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32132
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32132
    | exact resolve eq32132 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32132
  have eq32219 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32189 eq1000
    | exact resolve eq1000 eq32189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000 eq32189
  have eq32705 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq673 y x X0
       have i₂ := eq32179
       grind)
    | exact superpose eq32179 eq673
    | (have j0 := eq673 y x x
       grind)
    | exact resolve eq673 eq32179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673 eq32179
  have eq32710 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq32705 X0
       have i₂ := eq51 (σ y) X0
       grind)
    | exact superpose eq51 eq32705
    | exact resolve eq32705 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32705
  have eq32727 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq32710 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32710
    | (have j0 := eq32710 X0
       grind)
    | exact resolve eq32710 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32710
  have eq32733 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq32727 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32727
    | (have j0 := eq32727 X0
       grind)
    | exact resolve eq32727 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32727
  have eq32739 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq32733 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32733
    | (have j0 := eq32733 X0
       grind)
    | exact resolve eq32733 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32733
  have eq32746 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq32739
    | (have j0 := eq32739 X0
       grind)
    | exact resolve eq32739 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32739
  have eq32747 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq32746 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32746
  have eq32754 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32747 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32747
    | (have j0 := eq32747 X0
       grind)
    | exact resolve eq32747 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq32747
  have eq32762 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32754 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32754
    | (have j0 := eq32754 X0
       grind)
    | exact resolve eq32754 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32754
  have eq32878 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32219 eq119
    | exact resolve eq119 eq32219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq32219
  have eq32903 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq32878
    | exact resolve eq32878 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32878
  have eq33050 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq32903
       grind)
    | exact superpose eq32903 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq32903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32903
  have eq33063 : y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33050
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq33050
    | exact resolve eq33050 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33050
  have eq33064 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq33063
  have eq40246 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55 X0 x
       have i₂ := eq32762 (M.op X0 x)
       grind)
    | exact superpose eq32762 eq55
    | (have j1 := eq32762 X0
       grind)
    | exact resolve eq55 eq32762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32762
  have eq40314 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq40246
    | (have j0 := eq40246 X0
       grind)
    | exact resolve eq40246 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40246
  have eq40315 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq40314 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40314
  have eq40336 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq40315 eq51
    | exact resolve eq51 eq40315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40315
  have eq40664 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40336 eq27
    | (have j1 := eq40336 (σ x)
       grind)
    | exact resolve eq27 eq40336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq40336
  have eq40709 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq40664
  have eq40806 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq40709 eq28
    | exact resolve eq28 eq40709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq40709
  have eq56689 : ∀ X0 : G, (k X0 (M.op (M.op y X0) y)) = X0 ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq961 y X0 x
       have i₂ := eq33064
       grind)
    | exact superpose eq33064 eq961
    | exact resolve eq961 eq33064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq33064
  have eq56774 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq56689 X0
       have i₂ := eq51 y X0
       grind)
    | exact superpose eq51 eq56689
    | exact resolve eq56689 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56689
  have eq57863 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq55 x x
       have i₂ := eq56774 X0
       grind)
    | exact superpose eq56774 eq55
    | (have j1 := eq56774 X0
       grind)
    | exact resolve eq55 eq56774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56774
  have eq57973 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq57863 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57863
    | (have j0 := eq57863 X0
       grind)
    | exact resolve eq57863 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57863
  have eq57974 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq57973 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57973
  have eq58056 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19332
       have i₂ := eq57974 y
       grind)
    | exact superpose eq57974 eq19332
    | exact resolve eq19332 eq57974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19332 eq57974
  have eq58068 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq58056
  have eq58474 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq920 X0 y y
       have i₂ := eq58068
       grind)
    | exact superpose eq58068 eq920
    | exact resolve eq920 eq58068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq58068
  have eq58544 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq58474 x
       have i₂ := eq51 y x
       grind)
    | exact superpose eq51 eq58474
    | exact resolve eq58474 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq58474
  have eq60830 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq58544 x
       grind)
    | exact superpose eq58544 eq19
    | (have j1 := eq58544 x
       grind)
    | exact resolve eq19 eq58544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq58544
  have eq60951 : y = (M.op x y) := by grind
  clear eq60830
  have eq60974 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq60951 eq21
    | exact resolve eq21 eq60951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq60951
  have eq61170 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq60974
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq60974
    | exact resolve eq60974 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq60974
  have eq61177 : False := by grind
  exact eq61177

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_x_pxy_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq82 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq113 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq123 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq134 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq113
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq134
  have eq183 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq123 eq16
    | exact resolve eq16 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq237 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq183
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq183
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq239 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq237
  have eq626 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq55
    | (have j1 := eq88 X0 X1
       grind)
    | exact resolve eq55 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq952 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq61 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 x X0 y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8348 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq626 y y
       have i₂ := eq113
       grind)
    | exact superpose eq113 eq626
    | (have j0 := eq626 y y
       grind)
    | exact resolve eq626 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq626
  have eq8487 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq8348
  have eq8514 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq8487
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8487
    | exact resolve eq8487 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8487
  have eq8604 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq8514
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8514
    | exact resolve eq8514 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8514
  have eq26180 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26187 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq26180
    | exact resolve eq26180 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26180
  have eq26198 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq26187
       have r₂ := eq28
       grind)
    | exact resolve eq26187 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26187
  have eq26203 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26198 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq26198
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq26198
       grind)
    | exact resolve eq12 eq26198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26198
  have eq26252 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq26203
  have eq26253 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq26252
  have eq26717 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26253 eq82
    | exact resolve eq82 eq26253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq26253
  have eq26747 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq26717
    | exact resolve eq26717 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26717
  have eq26751 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq26747
       have r₂ := eq12 x y
       grind)
    | exact resolve eq26747 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26747
  have eq27063 : (σ y) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26751 eq66
    | exact resolve eq66 eq26751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27068 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26751 eq55
    | exact resolve eq55 eq26751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26751
  have eq27114 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq27068
    | exact resolve eq27068 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27068
  have eq27126 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq27114
       grind)
    | exact superpose eq27114 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq27114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27114
  have eq27134 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq27126
  have eq27142 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27134
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27134
    | exact resolve eq27134 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27134
  have eq27235 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27063 eq101
    | exact resolve eq101 eq27063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq27063
  have eq27253 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ x = (k x y) := by grind
  clear eq27235
  have eq27264 : x = (k x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq27253
       have r₂ := eq12 x y
       grind)
    | exact resolve eq27253 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27253
  have eq27279 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq27264
       grind)
    | exact superpose eq27264 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq27264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27264
  have eq27287 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq27279
  have eq27295 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq27287
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27287
    | exact resolve eq27287 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27287
  have eq28259 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 y x X0
       have i₂ := eq27142
       grind)
    | exact superpose eq27142 eq61
    | exact resolve eq61 eq27142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28337 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op x y) ∨ (M.op y X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28259 X0
       have i₂ := eq55 y X0
       grind)
    | exact superpose eq55 eq28259
    | exact resolve eq28259 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28259
  have eq28497 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq61 y x X0
       have i₂ := eq27295
       grind)
    | exact superpose eq27295 eq61
    | exact resolve eq61 eq27295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq27295
  have eq28575 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op x y) ∨ (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq28497 X0
       have i₂ := eq55 y X0
       grind)
    | exact superpose eq55 eq28497
    | exact resolve eq28497 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28497
  have eq29122 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op y X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq55 y y
       have i₂ := eq28337 X0
       grind)
    | exact superpose eq28337 eq55
    | (have j1 := eq28337 X0
       grind)
    | exact resolve eq55 eq28337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28337
  have eq29172 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq29122 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29122
    | (have j0 := eq29122 X0
       grind)
    | exact resolve eq29122 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29122
  have eq29191 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq55 y X0
       have i₂ := eq29172 X0
       grind)
    | exact superpose eq29172 eq55
    | exact resolve eq55 eq29172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29172
  have eq29420 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19
       have i₂ := eq29191 x
       grind)
    | exact superpose eq29191 eq19
    | (have j1 := eq29191 x
       grind)
    | exact resolve eq19 eq29191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29191
  have eq29457 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq29420
  have eq29461 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29457 eq28
    | exact resolve eq28 eq29457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29457
  have eq32675 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq55 y y
       have i₂ := eq28575 X0
       grind)
    | exact superpose eq28575 eq55
    | (have j1 := eq28575 X0
       grind)
    | exact resolve eq55 eq28575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28575
  have eq32731 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op y X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq32675 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32675
    | (have j0 := eq32675 X0
       grind)
    | exact resolve eq32675 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32675
  have eq32741 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq32731 X0
       grind)
    | (have r₁ := eq32731 X0
       have r₂ := eq29461
       grind)
    | exact resolve eq32731 eq29461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29461 eq32731
  have eq32766 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq55 y X0
       have i₂ := eq32741 X0
       grind)
    | exact superpose eq32741 eq55
    | exact resolve eq55 eq32741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq32741
  have eq33055 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq32766 x
       grind)
    | exact superpose eq32766 eq19
    | (have j1 := eq32766 x
       grind)
    | exact resolve eq19 eq32766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32766
  have eq33113 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq33055
  have eq33120 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33113 eq21
    | exact resolve eq21 eq33113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33123 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33113 eq56
    | exact resolve eq56 eq33113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33231 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq33113
  have eq33295 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33120
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33120
    | exact resolve eq33120 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33120
  have eq33679 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27142
       have i₂ := eq33123
       grind)
    | exact superpose eq33123 eq27142
    | exact resolve eq27142 eq33123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27142 eq33123
  have eq33742 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33679
  have eq33751 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq33742
       have r₂ := eq33231
       grind)
    | exact resolve eq33742 eq33231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33742
  have eq40159 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq141
       have i₂ := eq33751
       grind)
    | exact superpose eq33751 eq141
    | exact resolve eq141 eq33751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq33751
  have eq40257 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq40159
       have r₂ := eq33231
       grind)
    | exact resolve eq40159 eq33231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33231 eq40159
  have eq40262 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40257
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40257
    | exact resolve eq40257 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40257
  have eq40337 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33295 eq40262
    | exact resolve eq40262 eq33295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40356 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40262 eq8604
    | exact resolve eq8604 eq40262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8604 eq40262
  have eq40389 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq40337
  have eq40390 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq40356
    | exact resolve eq40356 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40356
  have eq40391 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq40390
  have eq40401 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq40389
       have r₂ := eq28
       grind)
    | exact resolve eq40389 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40389
  have eq41899 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33295 eq40391
    | exact resolve eq40391 eq33295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33295 eq40391
  have eq41976 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq41899
  have eq42006 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq41976
       have r₂ := eq28
       grind)
    | exact resolve eq41976 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41976
  have eq42017 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42006 eq66
    | exact resolve eq66 eq42006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42006
  have eq42140 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42017 eq40401
    | exact resolve eq40401 eq42017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40401 eq42017
  have eq42159 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq42140
  have eq42182 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42159 eq29
    | exact resolve eq29 eq42159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq42159
  have eq42400 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq42182
    | exact resolve eq42182 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq42182
  have eq42401 : x = (M.op x y) := by grind
  clear eq42400
  have eq42403 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq42401 eq21
    | exact resolve eq21 eq42401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq42406 : x = (M.op x x) := by
    first
    | exact superpose eq42401 eq56
    | exact resolve eq56 eq42401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42612 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq42403
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42403
    | exact resolve eq42403 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42403
  have eq42617 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq42612 eq27
    | exact resolve eq27 eq42612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq42837 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq952 x
       have i₂ := eq42406
       grind)
    | exact superpose eq42406 eq952
    | exact resolve eq952 eq42406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq42848 : x = (k x x) := by
    first
    | (have i₁ := eq66 x
       have i₂ := eq42406
       grind)
    | exact superpose eq42406 eq66
    | exact resolve eq66 eq42406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq42406
  have eq42948 : y = (M.op x y) := by
    first
    | exact superpose eq56 eq42837
    | exact resolve eq42837 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq42837
  have eq42961 : y = (M.op x y) := by
    first
    | (have i₁ := eq42948
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq42948
    | exact resolve eq42948 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq42948
  have eq42968 : x = y := by
    first
    | exact superpose eq42401 eq42961
    | exact resolve eq42961 eq42401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42961
  have eq42971 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq42968
       grind)
    | exact superpose eq42968 eq25
    | exact resolve eq25 eq42968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq42968
  have eq43209 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq42971
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42971
    | exact resolve eq42971 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42971
  have eq43276 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq42612 eq43209
    | exact resolve eq43209 eq42612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43209
  have eq45071 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq43276 eq42617
    | exact resolve eq42617 eq43276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42617 eq43276
  have eq45918 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45071 eq239
    | exact resolve eq239 eq45071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq45071
  have eq46019 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq45918
       have r₂ := eq28
       grind)
    | exact resolve eq45918 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45918
  have eq46039 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq42401 eq46019
    | exact resolve eq46019 eq42401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42401 eq46019
  have eq46054 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq46039
       have i₂ := eq42848
       grind)
    | exact superpose eq42848 eq46039
    | exact resolve eq46039 eq42848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42848 eq46039
  have eq46070 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46054 eq15
    | exact resolve eq15 eq46054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46054
  have eq46171 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46070
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq46070
    | exact resolve eq46070 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq46070
  have eq46208 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42612 eq46171
    | exact resolve eq46171 eq42612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42612 eq46171
  have eq46233 : False := by grind
  exact eq46233

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq57 eq55
    | exact resolve eq55 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq92 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq98 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq92
  have eq108 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq108
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq113
    | exact resolve eq113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq119
    | exact resolve eq119 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq120
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq120
    | exact resolve eq120 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq666 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq88 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq801 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq61 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 x X0 y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq61
    | (have j0 := eq61 (σ x) X0 (σ y)
       grind)
    | exact resolve eq61 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq12015 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq121 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12015
    | exact resolve eq12015 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12015
  have eq12027 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12016
       have r₂ := eq28
       grind)
    | exact resolve eq12016 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12016
  have eq12029 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12027
    | exact resolve eq12027 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12027
  have eq12034 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq12029
  have eq12072 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12034
    | exact resolve eq12034 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12034
  have eq15053 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12072 eq121
    | exact resolve eq121 eq12072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq12072
  have eq15068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15053
  have eq15071 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15068
       have r₂ := eq28
       grind)
    | exact resolve eq15068 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15068
  have eq15077 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq15084 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59 x x
       have i₂ := eq15071
       grind)
    | exact superpose eq15071 eq59
    | exact resolve eq59 eq15071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq15071
  have eq15120 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15084
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15084
    | exact resolve eq15084 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15084
  have eq15121 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15077
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15077
    | exact resolve eq15077 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15077
  have eq15346 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15120 eq57
    | exact resolve eq57 eq15120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15434 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq15121
       grind)
    | exact superpose eq15121 eq108
    | exact resolve eq108 eq15121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq15121
  have eq15458 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq15434
    | exact resolve eq15434 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15434
  have eq15501 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15346 eq805
    | exact resolve eq805 eq15346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15346
  have eq15566 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq57 eq15501
    | exact resolve eq15501 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15501
  have eq15572 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq15566
    | exact resolve eq15566 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15566
  have eq16488 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15572 eq15120
    | exact resolve eq15120 eq15572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15120 eq15572
  have eq16489 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16488
  have eq16797 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16489 eq30
    | exact resolve eq30 eq16489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16489
  have eq16940 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq16797
    | exact resolve eq16797 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16797
  have eq16941 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16940 eq21
    | exact resolve eq21 eq16940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16940
  have eq17066 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16941
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16941
    | exact resolve eq16941 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16941
  have eq17774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15458 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq15458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq17774
    | exact resolve eq17774 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17774
  have eq17796 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17785
       have r₂ := eq28
       grind)
    | exact resolve eq17785 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17785
  have eq17798 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq17796
    | exact resolve eq17796 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17796
  have eq17799 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17798
  have eq18172 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17799
  have eq18228 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq18172
    | exact resolve eq18172 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18172
  have eq18362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18228 eq15458
    | exact resolve eq15458 eq18228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15458 eq18228
  have eq18370 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18362
  have eq18378 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18370
       have r₂ := eq28
       grind)
    | exact resolve eq18370 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18370
  have eq18383 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18378 eq28
    | exact resolve eq28 eq18378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18385 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18378 eq57
    | exact resolve eq57 eq18378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18465 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18385 eq805
    | exact resolve eq805 eq18385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq18385
  have eq18536 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57 eq18465
    | exact resolve eq18465 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq18465
  have eq18543 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq18536
    | exact resolve eq18536 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18536
  have eq18670 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18543 eq28
    | exact resolve eq28 eq18543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18543
  have eq18707 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17066 eq18670
    | (have r₁ := eq18670
       have r₂ := eq17066
       grind)
    | exact resolve eq18670 eq17066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17066 eq18670
  have eq18710 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq18707
  have eq18711 : x = (M.op x y) ∨ x = y := by grind
  clear eq18710
  have eq19008 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq18711 eq56
    | exact resolve eq56 eq18711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19921 : y = (M.op (M.op (M.op x y) x) y) ∨ x = y := by
    first
    | (have i₁ := eq801 x
       have i₂ := eq19008
       grind)
    | exact superpose eq19008 eq801
    | exact resolve eq801 eq19008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801 eq19008
  have eq19989 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56 eq19921
    | exact resolve eq19921 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq19921
  have eq19996 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19989
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19989
    | exact resolve eq19989 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19989
  have eq20078 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq19996 eq18711
    | exact resolve eq18711 eq19996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18711 eq19996
  have eq20079 : x = y := by grind
  clear eq20078
  have eq20133 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq20079
       grind)
    | exact superpose eq20079 eq19
    | exact resolve eq19 eq20079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq20134 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20079
       grind)
    | exact superpose eq20079 eq25
    | exact resolve eq25 eq20079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20079
  have eq20249 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20134
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20134
    | exact resolve eq20134 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20134
  have eq20252 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20249 eq27
    | exact resolve eq27 eq20249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20249
  have eq20409 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq20133
       grind)
    | exact superpose eq20133 eq98
    | exact resolve eq98 eq20133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq20413 : (M.op x (M.op x y)) = (k (M.op x y) x) := by grind
  clear eq20133
  have eq20462 : (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq62 eq20413
    | exact resolve eq20413 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq20413
  have eq20464 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq20409
    | exact resolve eq20409 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20409
  have eq20499 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq20550 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq64 eq20499
    | exact resolve eq20499 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq20499
  have eq20640 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18378 eq20550
    | exact resolve eq20550 eq18378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18378 eq20550
  have eq21011 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20640 eq20464
    | exact resolve eq20464 eq20640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20464 eq20640
  have eq21032 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq21011
  have eq21042 : x = (M.op x y) := by
    first
    | (have r₁ := eq21032
       have r₂ := eq18383
       grind)
    | exact resolve eq21032 eq18383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18383 eq21032
  have eq21254 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21042 eq21
    | exact resolve eq21 eq21042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq21331 : x = (k x x) := by
    first
    | exact superpose eq21042 eq20462
    | exact resolve eq20462 eq21042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20462 eq21042
  have eq21411 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21254
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21254
    | exact resolve eq21254 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21254
  have eq21737 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq666 x x
       have i₂ := eq21331
       grind)
    | exact superpose eq21331 eq666
    | (have j0 := eq666 x x
       grind)
    | exact resolve eq666 eq21331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq21331
  have eq21740 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21737
  have eq21741 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21740
  have eq21755 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21741
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21741
    | exact resolve eq21741 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21741
  have eq21774 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20252 eq21755
    | exact resolve eq21755 eq20252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20252 eq21755
  have eq21788 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21411 eq21774
    | exact resolve eq21774 eq21411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21411 eq21774
  have eq21802 : False := by grind
  exact eq21802

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_y_pyy_pxy_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
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
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (M.op X0 X1) X0
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq33
    | exact resolve eq33 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq70 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
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
  have eq97 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq37 X1 X2 X0
       grind)
    | exact superpose eq37 eq33
    | exact resolve eq33 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq16
    | (have j1 := eq68 x y
       grind)
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op (M.op (M.op (σ (k X0 X1)) X2) (σ X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq9
    | (have j1 := eq68 X1 X1
       grind)
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq180 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq167 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq182 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq180 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq180 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq189 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 (τ X0) X1
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq191 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq189
    | (have j0 := eq189 X0 X1
       grind)
    | exact resolve eq189 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq194 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq191
    | (have j0 := eq191 X0 X1
       grind)
    | exact resolve eq191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq538 : ∀ X0 X1 X2 : G, (k (σ X2) (k X0 (σ X1))) = (σ (k X2 (M.op (τ X0) X1))) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (M.op (τ X0) X1)
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq15
    | (have j1 := eq70 X0 X1
       grind)
    | exact resolve eq15 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq557 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (σ (k X2 (M.op (τ X0) X1))) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq538 X0 X1 X2
       have i₂ := eq20 X0 X1 X2
       grind)
    | exact superpose eq20 eq538
    | (have j0 := eq538 X0 X1 X2
       grind)
    | exact resolve eq538 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq538
  have eq889 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) X1)) X0) ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 (M.op (τ X0) X1) X0
       have i₂ := eq33 (τ X0) X1
       grind)
    | exact superpose eq33 eq71
    | (have j0 := eq71 (M.op (τ X0) X1) X0
       grind)
    | exact resolve eq71 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq920 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) X1)) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq889 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq889
    | (have j0 := eq889 X0 X1
       grind)
    | exact resolve eq889 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq932 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) X1)) X0) = X0 ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq920 X0 X1
       have i₂ := eq35 (τ X0) X1
       grind)
    | exact superpose eq35 eq920
    | (have j0 := eq920 X0 X1
       grind)
    | exact resolve eq920 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq1140 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq166
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq166
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq166 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq1141 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq1140
  have eq2129 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (M.op (M.op (σ (k X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq2130 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (M.op (M.op (σ (k X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2129 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2129
  have eq5583 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op (σ (k (τ X0) (τ X0))) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2130 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2130
    | exact resolve eq2130 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq5683 : ∀ X0 X1 : G, (M.op (M.op (M.op (k (σ (τ X0)) X0) X1) X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5583 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq5583
    | (have j0 := eq5583 X0 X1
       grind)
    | exact resolve eq5583 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5583
  have eq5688 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 X0) X1) X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5683 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5683
    | (have j0 := eq5683 X0 X1
       grind)
    | exact resolve eq5683 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5683
  have eq5703 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (k X0 X0) (k X0 X0) X1
       have i₂ := eq5688 X0 (k X0 X0)
       grind)
    | exact superpose eq5688 eq31
    | (have j1 := eq5688 X0 X1
       grind)
    | exact resolve eq31 eq5688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq5688
  have eq6236 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq97 X0 X0 X0
       have i₂ := eq5703 X0 X1
       grind)
    | exact superpose eq5703 eq97
    | (have j1 := eq5703 X0 X2
       grind)
    | exact resolve eq97 eq5703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5703
  have eq6330 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6236 X0 X1 X2
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq6236
    | (have j0 := eq6236 X0 X1 X2
       grind)
    | exact resolve eq6236 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6236
  have eq6978 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq6330 X0 (M.op (M.op X0 X0) (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6330
  have eq6979 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq6978 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6978
  have eq7332 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0) X0 X0
       have i₂ := eq6979 X0
       grind)
    | exact superpose eq6979 eq9
    | exact resolve eq9 eq6979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7334 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 (k X0 X0) X0 X0
       have i₂ := eq6979 X0
       grind)
    | exact superpose eq6979 eq34
    | exact resolve eq34 eq6979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6979
  have eq7438 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq7334 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq7334
    | exact resolve eq7334 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7439 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7334 (τ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq7334
    | exact resolve eq7334 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7446 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k X0 X0)) = (M.op X1 (M.op (M.op X0 X1) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (k X0 X0) X0
       have i₂ := eq7334 X0
       grind)
    | exact superpose eq7334 eq34
    | exact resolve eq34 eq7334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq8226 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (k X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 (τ (k X0 X0)) (τ X0) X1
       have i₂ := eq7439 X0
       grind)
    | exact superpose eq7439 eq37
    | exact resolve eq37 eq7439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq8477 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X0)) X1))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ (M.op (τ (σ X0)) X1)) X0
       have i₂ := eq932 (σ X0) X1
       grind)
    | exact superpose eq932 eq22
    | (have j1 := eq932 (σ X0) X1
       grind)
    | exact resolve eq22 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq8517 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) X1) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8477 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq10 eq8477
    | (have j0 := eq8477 X0 X1
       grind)
    | exact resolve eq8477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8477
  have eq8553 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8517 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8517
    | (have j0 := eq8517 X0 X1
       grind)
    | exact resolve eq8517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8517
  have eq8569 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k (M.op X0 X1) X0) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8553 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8553
    | (have j0 := eq8553 X0 X1
       grind)
    | exact resolve eq8553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8553
  have eq8585 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8569 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8569
    | (have j0 := eq8569 X0 X1
       grind)
    | exact resolve eq8569 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8569
  have eq8595 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq8585 X0 X1
       have j1 := eq12 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq8585 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq8585 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq8585 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8585
  have eq8787 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8595 X0 (k X0 X0)
       have i₂ := eq7332 X0
       grind)
    | exact superpose eq7332 eq8595
    | exact resolve eq8595 eq7332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7332
  have eq8813 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8595 (M.op X0 X1) X0
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq8595
    | (have j0 := eq8595 X0 X1
       grind)
    | exact resolve eq8595 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8838 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) X1)) X0) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) X1)
       have i₂ := eq8595 (τ X0) X1
       grind)
    | exact superpose eq8595 eq18
    | (have j1 := eq8595 (τ X0) X1
       grind)
    | exact resolve eq18 eq8595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8595
  have eq8875 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) X1)) X0) = X0 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8838 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8838
    | (have j0 := eq8838 X0 X1
       grind)
    | exact resolve eq8838 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8838
  have eq8888 : ∀ X0 : G, (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8787 X0
       have j1 := eq194 X0 (k X0 X0)
       grind)
    | (have r₁ := eq8787 X0
       have r₂ := eq194 X0 x
       grind)
    | exact resolve eq8787 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq8787
  have eq9083 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8888 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq8888
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq8888 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8888
  have eq9131 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq9083 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9083
  have eq9169 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq9131 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq9131 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq9131 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9131
  have eq9258 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq9169 (τ X0)
       grind)
    | exact superpose eq9169 eq18
    | exact resolve eq18 eq9169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9169
  have eq9296 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9258 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9258
    | exact resolve eq9258 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9258
  have eq9610 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq9296 (τ X0)
       grind)
    | exact superpose eq9296 eq18
    | exact resolve eq18 eq9296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9296
  have eq9649 : ∀ X0 : G, (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9610 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9610
    | exact resolve eq9610 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9610
  have eq12164 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))
       have i₂ := eq9649 (τ X0)
       grind)
    | exact superpose eq9649 eq18
    | exact resolve eq18 eq9649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9649
  have eq12203 : ∀ X0 : G, (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12164 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12164
    | exact resolve eq12164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12164
  have eq13868 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq35 y x
       have i₂ := eq1141
       grind)
    | exact superpose eq1141 eq35
    | exact resolve eq35 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq13939 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq13868
  have eq19666 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op X0 X1)) (σ X0)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8875 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8875
    | exact resolve eq8875 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8875
  have eq19786 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op X0 X1) X0)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19666 X0 X1
       have i₂ := eq15 (M.op X0 X1) X0
       grind)
    | exact superpose eq15 eq19666
    | (have j0 := eq19666 X0 X1
       grind)
    | exact resolve eq19666 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19666
  have eq19901 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19786 (k X0 X0) X0
       have i₂ := eq7334 X0
       grind)
    | exact superpose eq7334 eq19786
    | exact resolve eq19786 eq7334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7334 eq19786
  have eq22741 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (σ (k (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19901 (τ X0)
       have i₂ := eq557 X0 (τ X0) (τ X0)
       grind)
    | exact superpose eq557 eq19901
    | (have j0 := eq19901 (τ X0)
       have j1 := eq557 X0 (τ X0) x
       grind)
    | exact resolve eq19901 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq19901
  have eq22821 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (σ (k (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq22741 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22741
  have eq22858 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (σ (k (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq22821 X0
       have j1 := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq22821 X0
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq22821 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22821
  have eq22877 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq22858 X0
       have i₂ := eq17 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq17 eq22858
    | (have j0 := eq22858 X0
       grind)
    | exact resolve eq22858 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq22858
  have eq22895 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq22877 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq22877
    | (have j0 := eq22877 X0
       grind)
    | exact resolve eq22877 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22877
  have eq22905 : ∀ X0 : G, (k X0 X0) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq22895 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22895
    | (have j0 := eq22895 X0
       grind)
    | exact resolve eq22895 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22895
  have eq22907 : ∀ X0 : G, (k X0 X0) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22905 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq22905
    | (have j0 := eq22905 X0
       grind)
    | exact resolve eq22905 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22905
  have eq90223 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq22907 (σ X0)
       grind)
    | exact superpose eq22907 eq28
    | (have j1 := eq22907 (σ X0)
       grind)
    | exact resolve eq28 eq22907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq22907
  have eq90325 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq90223 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq90223
    | (have j0 := eq90223 X0
       grind)
    | exact resolve eq90223 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90223
  have eq90380 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (τ (k (σ X0) (σ X0))) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq90325 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90325
    | (have j0 := eq90325 X0
       grind)
    | exact resolve eq90325 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90325
  have eq90432 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (k (τ (σ X0)) X0) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq90380 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq90380
    | (have j0 := eq90380 X0
       grind)
    | exact resolve eq90380 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90380
  have eq90457 : ∀ X0 : G, (k X0 X0) = (k X0 (M.op X0 X0)) ∨ (τ (σ X0)) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq90432 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90432
    | (have j0 := eq90432 X0
       grind)
    | exact resolve eq90432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90432
  have eq90475 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (k X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90457 X0
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq90457
    | (have j0 := eq90457 X0
       grind)
    | exact resolve eq90457 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90457
  have eq90488 : ∀ X0 : G, (k X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq90475 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90475
    | (have j0 := eq90475 X0
       grind)
    | exact resolve eq90475 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90475
  have eq90825 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq90488 X0
       have i₂ := eq8813 X0 X0
       grind)
    | exact superpose eq8813 eq90488
    | (have j0 := eq90488 X0
       have j1 := eq8813 X0 X0
       grind)
    | exact resolve eq90488 eq8813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8813 eq90488
  have eq90993 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq90825 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq90825 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq90825 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90825
  have eq92694 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq90993 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq90993
    | exact resolve eq90993 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90993
  have eq115531 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq92694 X0
       grind)
    | exact superpose eq92694 eq10
    | (have j1 := eq92694 X0
       grind)
    | exact resolve eq10 eq92694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92694
  have eq115723 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq115531 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq115531
    | (have j0 := eq115531 X0
       grind)
    | exact resolve eq115531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115531
  have eq115980 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7446 X0 X1
       have i₂ := eq115723 X0
       grind)
    | exact superpose eq115723 eq7446
    | (have j1 := eq115723 X0
       grind)
    | exact resolve eq7446 eq115723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116000 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ X0) X1) (τ X0)) X1) = X1 ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8226 X0 X1
       have i₂ := eq115723 X0
       grind)
    | exact superpose eq115723 eq8226
    | (have j1 := eq115723 X0
       grind)
    | exact resolve eq8226 eq115723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8226 eq115723
  have eq116332 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq116000 X0 X1
       have i₂ := eq33 (τ X0) X1
       grind)
    | exact superpose eq33 eq116000
    | (have j0 := eq116000 X0 X1
       grind)
    | exact resolve eq116000 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116000
  have eq116345 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq115980 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq115980
    | (have j0 := eq115980 X0 X1
       grind)
    | exact resolve eq115980 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115980
  have eq122557 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq116345 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq116345
    | (have j0 := eq116345 (τ X0) X1
       grind)
    | exact resolve eq116345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116345
  have eq123080 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq122557 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq122557
    | (have j0 := eq122557 X0 X1
       grind)
    | exact resolve eq122557 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122557
  have eq123130 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq123080 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq123080
    | (have j0 := eq123080 X0 X1
       grind)
    | exact resolve eq123080 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123080
  have eq123631 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7439 X0
       have i₂ := eq123130 X0 X1
       grind)
    | exact superpose eq123130 eq7439
    | (have j1 := eq123130 X0 (τ (M.op X0 X0))
       grind)
    | exact resolve eq7439 eq123130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7439 eq123130
  have eq130957 : ∀ X0 : G, (k (σ (σ (σ (τ (τ (τ X0)))))) X0) = X0 ∨ (σ (k (τ (τ X0)) (τ (τ X0)))) = (M.op (σ (τ (τ X0))) (σ (τ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq12203 X0
       have i₂ := eq116332 (τ (τ X0)) (τ (τ (τ X0)))
       grind)
    | exact superpose eq116332 eq12203
    | (have j1 := eq116332 (τ (τ X0)) x
       grind)
    | exact resolve eq12203 eq116332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12203 eq116332
  have eq131194 : ∀ X0 : G, (k (σ (σ (τ (τ X0)))) X0) = X0 ∨ (σ (k (τ (τ X0)) (τ (τ X0)))) = (M.op (σ (τ (τ X0))) (σ (τ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq130957 X0
       have i₂ := eq11 (τ (τ X0))
       grind)
    | exact superpose eq11 eq130957
    | (have j0 := eq130957 X0
       grind)
    | exact resolve eq130957 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130957
  have eq131208 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (σ (k (τ (τ X0)) (τ (τ X0)))) = (M.op (σ (τ (τ X0))) (σ (τ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq131194 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq131194
    | (have j0 := eq131194 X0
       grind)
    | exact resolve eq131194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131194
  have eq131215 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k (τ (τ X0)) (τ (τ X0)))) = (M.op (σ (τ (τ X0))) (σ (τ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq131208 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq131208
    | (have j0 := eq131208 X0
       grind)
    | exact resolve eq131208 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131208
  have eq131221 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (σ (k (τ (τ X0)) (τ (τ X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq131215 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq131215
    | (have j0 := eq131215 X0
       grind)
    | exact resolve eq131215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131215
  have eq131223 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (σ (τ (τ X0))) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq131221 X0
       have i₂ := eq18 (τ X0) (τ (τ X0))
       grind)
    | exact superpose eq18 eq131221
    | (have j0 := eq131221 X0
       grind)
    | exact resolve eq131221 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq131221
  have eq131224 : ∀ X0 : G, (k (τ X0) (τ X0)) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq131223 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq131223
    | (have j0 := eq131223 X0
       grind)
    | exact resolve eq131223 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131223
  have eq131225 : ∀ X0 : G, (k X0 X0) = X0 ∨ (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq131224 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq131224
    | (have j0 := eq131224 X0
       grind)
    | exact resolve eq131224 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq131224
  have eq131305 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7446 X0 X1
       have i₂ := eq131225 X0
       grind)
    | exact superpose eq131225 eq7446
    | (have j1 := eq131225 X0
       grind)
    | exact resolve eq7446 eq131225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7446 eq131225
  have eq131698 : ∀ X0 X1 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq131305 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq131305
    | (have j0 := eq131305 X0 X1
       grind)
    | exact resolve eq131305 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131305
  have eq137824 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq131698 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq131698
    | (have j0 := eq131698 (σ X0) X1
       grind)
    | exact resolve eq131698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131698
  have eq138307 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq137824 X0 X1
       have i₂ := eq22 (σ X0) X0
       grind)
    | exact superpose eq22 eq137824
    | (have j0 := eq137824 X0 X1
       grind)
    | exact resolve eq137824 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq137824
  have eq138364 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq138307 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq138307
    | (have j0 := eq138307 X0 X1
       grind)
    | exact resolve eq138307 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138307
  have eq138966 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7438 X0
       have i₂ := eq138364 X0 X1
       grind)
    | exact superpose eq138364 eq7438
    | (have j1 := eq138364 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq7438 eq138364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7438 eq138364
  have eq197159 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq123631 X0 (τ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123631
  have eq197160 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq197159 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197159
  have eq197962 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq33 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq197160 X0
       grind)
    | exact superpose eq197160 eq33
    | exact resolve eq33 eq197160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197160
  have eq220426 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq138966 X0 (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138966
  have eq220427 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq220426 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220426
  have eq221236 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq33 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq220427 X0
       grind)
    | exact superpose eq220427 eq33
    | exact resolve eq33 eq220427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220427
  have eq345226 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq35 (σ y) (σ x)
       have i₂ := eq13939
       grind)
    | exact superpose eq13939 eq35
    | exact resolve eq35 eq13939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq13939
  have eq345443 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq345226
  have eq345739 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq221236 y
       have i₂ := eq345443
       grind)
    | exact superpose eq345443 eq221236
    | exact resolve eq221236 eq345443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221236 eq345443
  have eq345965 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq345739
  have eq346195 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq197962 (σ y)
       have i₂ := eq345965
       grind)
    | exact superpose eq345965 eq197962
    | exact resolve eq197962 eq345965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197962
  have eq346226 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq97 X0 (σ y) (σ y)
       have i₂ := eq345965
       grind)
    | exact superpose eq345965 eq97
    | exact resolve eq97 eq345965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345965
  have eq346482 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq346226 x
       have i₂ := eq33 (σ y) x
       grind)
    | exact superpose eq33 eq346226
    | exact resolve eq346226 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346226
  have eq346503 : y = (M.op y y) := by
    first
    | (have i₁ := eq346195
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq346195
    | exact resolve eq346195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346195
  have eq347045 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) := by
    intro X0
    first
    | (have i₁ := eq97 X0 y y
       have i₂ := eq346503
       grind)
    | exact superpose eq346503 eq97
    | exact resolve eq97 eq346503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq346503
  have eq347300 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq347045 x
       have i₂ := eq33 y x
       grind)
    | exact superpose eq33 eq347045
    | exact resolve eq347045 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq347045
  have eq356509 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq346482 (σ x)
       grind)
    | exact superpose eq346482 eq16
    | exact resolve eq16 eq346482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346482
  have eq356629 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq356509
       have i₂ := eq347300 x
       grind)
    | exact superpose eq347300 eq356509
    | exact resolve eq356509 eq347300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347300 eq356509
  have eq356630 : False := by grind
  exact eq356630

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_y_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X0 X1) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq170 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72 x y
       grind)
    | exact superpose eq72 eq16
    | (have j1 := eq72 x y
       grind)
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq181 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq72 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq182 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq181 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq185 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq178 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq187 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq185 X0
       have j1 := eq182 X0
       grind)
    | (have r₁ := eq185 X0
       have r₂ := eq182 X0
       grind)
    | exact resolve eq185 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq185
  have eq190 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq187 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq187
    | (have j0 := eq187 X0
       grind)
    | exact resolve eq187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq451 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq190 (τ X0)
       grind)
    | exact superpose eq190 eq19
    | (have j1 := eq190 (τ X0)
       grind)
    | exact resolve eq19 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq490 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq451 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq451
    | (have j0 := eq451 X0
       grind)
    | exact resolve eq451 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq451
  have eq497 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq490 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq490
    | (have j0 := eq490 X0
       grind)
    | exact resolve eq490 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq500 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq497 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq497
    | (have j0 := eq497 X0
       grind)
    | exact resolve eq497 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq514 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 (k X0 X0) X0
       have i₂ := eq500 X0
       grind)
    | exact superpose eq500 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq500 X0
       grind)
    | exact resolve eq14 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq523 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq514 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq534 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq523 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq523 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq523 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq563 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq24 X0 (k X0 X0)
       have i₂ := eq534 X0
       grind)
    | exact superpose eq534 eq24
    | (have j1 := eq534 X0
       grind)
    | exact resolve eq24 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq574 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq563 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq563 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq563 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq665 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq574 (σ X0)
       grind)
    | exact superpose eq574 eq15
    | exact resolve eq15 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq665 X0
       have i₂ := eq574 X0
       grind)
    | exact superpose eq574 eq665
    | exact resolve eq665 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq665
  have eq821 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) (σ X0)
       have i₂ := eq684 X0
       grind)
    | exact superpose eq684 eq24
    | exact resolve eq24 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) (σ X0) X1
       have i₂ := eq684 X0
       grind)
    | exact superpose eq684 eq26
    | exact resolve eq26 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1672 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq170
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq170
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq170 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq1673 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq1672
  have eq1674 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1673
       have i₂ := eq684 x
       grind)
    | exact superpose eq684 eq1673
    | exact resolve eq1673 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq1675 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1674
       have i₂ := eq684 x
       grind)
    | exact superpose eq684 eq1674
    | exact resolve eq1674 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq1674
  have eq29388 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1675
       grind)
    | exact superpose eq1675 eq10
    | exact resolve eq10 eq1675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1675
  have eq29472 : y = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29388
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq29388
    | exact resolve eq29388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29388
  have eq29473 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq29472
  have eq29510 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq29473
       grind)
    | exact superpose eq29473 eq10
    | exact resolve eq10 eq29473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29473
  have eq29598 : x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq29510
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29510
    | exact resolve eq29510 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29510
  have eq29599 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq29598
  have eq29649 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq821 x
       have i₂ := eq29599
       grind)
    | exact superpose eq29599 eq821
    | exact resolve eq821 eq29599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq29737 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq29599
       grind)
    | exact superpose eq29599 eq24
    | exact resolve eq24 eq29599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq29599
  have eq32546 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29649
       grind)
    | exact superpose eq29649 eq16
    | exact resolve eq16 eq29649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29649
  have eq32813 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq32546
       have i₂ := eq29737
       grind)
    | exact superpose eq29737 eq32546
    | exact resolve eq32546 eq29737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29737 eq32546
  have eq32814 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by grind
  clear eq32813
  have eq32815 : x = (M.op x x) := by grind
  clear eq32814
  have eq32832 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq822 x X0
       have i₂ := eq32815
       grind)
    | exact superpose eq32815 eq822
    | exact resolve eq822 eq32815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq32900 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26 x x X0
       have i₂ := eq32815
       grind)
    | exact superpose eq32815 eq26
    | exact resolve eq26 eq32815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq32815
  have eq32969 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32900 X0
       have i₂ := eq22 x X0
       grind)
    | exact superpose eq22 eq32900
    | exact resolve eq32900 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32900
  have eq33025 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32832 X0
       have i₂ := eq22 (σ x) X0
       grind)
    | exact superpose eq22 eq32832
    | exact resolve eq32832 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq32832
  have eq34098 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33025 (σ y)
       grind)
    | exact superpose eq33025 eq16
    | exact resolve eq16 eq33025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33025
  have eq34299 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq34098
       have i₂ := eq32969 y
       grind)
    | exact superpose eq32969 eq34098
    | exact resolve eq34098 eq32969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32969 eq34098
  have eq34300 : False := by grind
  exact eq34300

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq27 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
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
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq105 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 (M.op X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq14 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq108 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq110 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq105 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq111 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq109 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq109 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq109 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq111 X0
       have i₂ := eq66 X0 X0
       grind)
    | exact superpose eq66 eq111
    | exact resolve eq111 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq111
  have eq116 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq114 (τ X0)
       grind)
    | exact superpose eq114 eq19
    | exact resolve eq19 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq114 (σ X0)
       grind)
    | exact superpose eq114 eq23
    | exact resolve eq23 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq114
  have eq202 : ∀ X0 X1 X2 X3 : G, (σ (k (k X0 (τ X1)) (k X2 (τ X3)))) = (k (k (σ X0) X1) (k (σ X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27 X2 X3 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq27
    | exact resolve eq27 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq784 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq110 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq785 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq784 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq800 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq785 X1 (τ X0)
       grind)
    | exact superpose eq785 eq19
    | (have j1 := eq785 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq804 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq785 (σ X1) (σ X0)
       grind)
    | exact superpose eq785 eq15
    | (have j1 := eq785 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq785 (σ X1) X0
       grind)
    | exact superpose eq785 eq29
    | (have j1 := eq785 (k X1 (τ X0)) (τ (M.op X0 (σ X1)))
       grind)
    | exact resolve eq29 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq870 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq800 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq800
    | exact resolve eq800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq906 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq870 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq870
    | (have j0 := eq870 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq870 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq969 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq809 (M.op (σ X0) X1) X0
       have i₂ := eq64 (σ X0) X1
       grind)
    | exact superpose eq64 eq809
    | (have j0 := eq809 (M.op (σ X0) X1) X0
       grind)
    | exact resolve eq809 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq984 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq969 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq969
    | (have j0 := eq969 X0 X1
       grind)
    | exact resolve eq969 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq1062 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq804 x y
       grind)
    | exact superpose eq804 eq16
    | (have j1 := eq804 x y
       grind)
    | exact resolve eq16 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1068 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (σ X1) (σ X0)
       have i₂ := eq804 X1 X0
       grind)
    | exact superpose eq804 eq64
    | (have j1 := eq804 X0 X1
       grind)
    | exact resolve eq64 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq1087 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1062
       have i₂ := eq906 x y
       grind)
    | exact superpose eq906 eq1062
    | (have j1 := eq906 (σ x) (σ y)
       grind)
    | (have r₁ := eq1062
       have r₂ := eq906 x y
       grind)
    | (have r₁ := eq1062
       have r₂ := eq906 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1062
       have r₂ := eq906 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1062 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906 eq1062
  have eq1088 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1087
  have eq1092 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1088
       grind)
    | exact superpose eq1088 eq16
    | exact resolve eq16 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1146 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ (k X0 X1))) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1068 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq1068
    | (have j0 := eq1068 (τ X0) (τ X1)
       grind)
    | exact resolve eq1068 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1068
  have eq1183 : ∀ X0 X1 : G, (M.op (σ (τ (k X0 X1))) X1) = X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1146 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1146
    | (have j0 := eq1146 X0 X1
       grind)
    | exact resolve eq1146 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1186 : ∀ X0 X1 : G, (M.op (k X0 X1) X1) = X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1183 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1183
    | (have j0 := eq1183 X0 X1
       grind)
    | exact resolve eq1183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1187 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op (k X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1186 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1186
    | (have j0 := eq1186 X0 X1
       grind)
    | exact resolve eq1186 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1188 : ∀ X0 X1 : G, (M.op (k X0 X1) X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1187 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1187
    | (have j0 := eq1187 X0 X1
       grind)
    | exact resolve eq1187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1205 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 (k X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 (k X1 X0) X0
       have i₂ := eq1188 X1 X0
       grind)
    | exact superpose eq1188 eq64
    | (have j1 := eq1188 (k X1 X0) (M.op X0 (k X1 X0))
       grind)
    | exact resolve eq64 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1207 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (k X1 X0) X2) X0) X2) = X2 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 (k X1 X0) X0 X2
       have i₂ := eq1188 X1 X0
       grind)
    | exact superpose eq1188 eq68
    | (have j1 := eq1188 (M.op (M.op (M.op (k X1 X0) X2) X0) X2) X2
       grind)
    | exact resolve eq68 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1650 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (k X0 (τ (M.op (σ X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 (σ X0) X2 X1
       have i₂ := eq984 X0 X2
       grind)
    | exact superpose eq984 eq68
    | (have j1 := eq984 X0 X2
       grind)
    | exact resolve eq68 eq984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1673 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (σ X0) X2))) = X0 ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1650 X0 X1 X2
       have i₂ := eq64 (σ X0) X1
       grind)
    | exact superpose eq64 eq1650
    | (have j0 := eq1650 X0 X1 X2
       grind)
    | exact resolve eq1650 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650
  have eq1913 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (τ (M.op (σ (τ X0)) X1)))) ∨ (M.op (σ (τ X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (τ (M.op (σ (τ X0)) X1))
       have i₂ := eq1673 (τ X0) X2 X1
       grind)
    | exact superpose eq1673 eq18
    | (have j1 := eq1673 (τ X0) X2 X2
       grind)
    | exact resolve eq18 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq1918 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (M.op (σ (τ X0)) X1)) ∨ (M.op (σ (τ X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1913 X0 X1 X2
       have i₂ := eq11 (M.op (σ (τ X0)) X1)
       grind)
    | exact superpose eq11 eq1913
    | (have j0 := eq1913 X0 X1 X2
       grind)
    | exact resolve eq1913 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1913
  have eq1932 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op (σ (τ X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1918 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1918
    | (have j0 := eq1918 X0 X1 X2
       grind)
    | exact resolve eq1918 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1918
  have eq1935 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1932 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1932
    | (have j0 := eq1932 X0 X1 X2
       grind)
    | exact resolve eq1932 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq1976 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) ∨ (M.op (τ X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) X1)
       have i₂ := eq1935 (τ X0) X1 X2
       grind)
    | exact superpose eq1935 eq18
    | (have j1 := eq1935 (τ X0) X1 X2
       grind)
    | exact resolve eq18 eq1935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935
  have eq1981 : ∀ X0 X1 X2 : G, (M.op (τ X0) X2) = X2 ∨ (k X0 (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1976 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1976
    | (have j0 := eq1976 X0 X1 X2
       grind)
    | exact resolve eq1976 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1976
  have eq2266 : ∀ X0 X1 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (σ (k (k X0 (τ X1)) (k X0 (τ X1)))) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2275 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (k X0 (τ (σ (k X0 X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq984 X0 (σ X0)
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq984
    | (have j0 := eq984 X0 (σ X0)
       have j1 := eq90 X0
       grind)
    | exact resolve eq984 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq2279 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq90 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq90 X0
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2299 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq90 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq2305 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2279 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq2279 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq2279 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2279
  have eq2308 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2275 X0
       have j1 := eq2299 X0
       grind)
    | (have r₁ := eq2275 X0
       have r₂ := eq2299 X0
       grind)
    | exact resolve eq2275 eq2299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq2312 : ∀ X0 X1 : G, (k (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2266 X0 X1
       have i₂ := eq202 X0 X1 X0 X1
       grind)
    | exact superpose eq202 eq2266
    | (have j0 := eq2266 X0 X1
       grind)
    | exact resolve eq2266 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq2266
  have eq2320 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2308 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq2308
    | (have j0 := eq2308 X0
       grind)
    | exact resolve eq2308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308
  have eq2321 : ∀ X0 X1 : G, (k (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2312 X0 X1
       have j1 := eq12 (k (σ X0) X1) (k (σ X0) X1)
       grind)
    | (have r₁ := eq2312 X0 X1
       have r₂ := eq12 X0 (k (σ X0) X1)
       grind)
    | exact resolve eq2312 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312
  have eq2331 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2299 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq2299
    | (have j0 := eq2299 (τ X0)
       grind)
    | exact resolve eq2299 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2299
  have eq2333 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2331 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2331
    | (have j0 := eq2331 X0
       grind)
    | exact resolve eq2331 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2331
  have eq2336 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2333 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2333
    | (have j0 := eq2333 X0
       grind)
    | exact resolve eq2333 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2333
  have eq2406 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (k (τ X0) (τ X0))
       have i₂ := eq2320 (τ X0)
       grind)
    | exact superpose eq2320 eq18
    | (have j1 := eq2320 (τ X0)
       grind)
    | exact resolve eq18 eq2320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2320
  have eq2412 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2406 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq2406
    | (have j0 := eq2406 X0
       grind)
    | exact resolve eq2406 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2406
  have eq2429 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2412 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2412
    | (have j0 := eq2412 X0
       grind)
    | exact resolve eq2412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412
  have eq2437 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2429 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2429
    | (have j0 := eq2429 X0
       grind)
    | exact resolve eq2429 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2429
  have eq2464 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1207 (k X0 X0) X0 X1
       have i₂ := eq2437 X0
       grind)
    | exact superpose eq2437 eq1207
    | (have j0 := eq1207 (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) X1 x
       have j1 := eq2437 X0
       grind)
    | exact resolve eq1207 eq2437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207 eq2437
  have eq2491 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2464 X0 X1
       have j1 := eq2336 X0
       grind)
    | (have r₁ := eq2464 X0 X1
       have r₂ := eq2336 X0
       grind)
    | exact resolve eq2464 eq2336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336 eq2464
  have eq2950 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (k X0 (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0
       have i₂ := eq1981 X0 X1 (τ X0)
       grind)
    | exact superpose eq1981 eq116
    | (have j1 := eq1981 X0 X1 x
       grind)
    | exact resolve eq116 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1981
  have eq2984 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 (σ (M.op (τ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2950 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2950
    | (have j0 := eq2950 X0 X1
       grind)
    | exact resolve eq2950 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2950
  have eq3754 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2305 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq2305
    | (have j0 := eq2305 (τ X0) X1
       grind)
    | exact resolve eq2305 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2305
  have eq3758 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3754 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3754
    | (have j0 := eq3754 X0 X1
       grind)
    | exact resolve eq3754 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3754
  have eq3761 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3758 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3758
    | (have j0 := eq3758 X0 X1
       grind)
    | exact resolve eq3758 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3758
  have eq7091 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X1 ∨ (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X0 X1
       have i₂ := eq2491 X0 X2
       grind)
    | exact superpose eq2491 eq68
    | (have j1 := eq2491 X0 X2
       grind)
    | exact resolve eq68 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq2491
  have eq7148 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7091 X0 X1 X2
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq7091
    | (have j0 := eq7091 X0 X1 X2
       grind)
    | exact resolve eq7091 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7091
  have eq9213 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X0) X0 X0
       have i₂ := eq7148 X0 X1 X0
       grind)
    | exact superpose eq7148 eq9
    | (have j1 := eq7148 X0 (k X0 X0) x
       grind)
    | exact resolve eq9 eq7148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7148
  have eq9407 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq9213 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9213
  have eq9408 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq9407 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9407
  have eq9457 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq64 X0 (k X0 X0)
       have i₂ := eq9408 X0
       grind)
    | exact superpose eq9408 eq64
    | exact resolve eq64 eq9408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9408
  have eq9557 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9457 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq9457
    | exact resolve eq9457 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9457
  have eq9657 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (k X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (k X0 X0)) (σ X0)
       have i₂ := eq9557 X0
       grind)
    | exact superpose eq9557 eq9
    | exact resolve eq9 eq9557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9557
  have eq11199 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (k X0 (σ (M.op (τ X0) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9657 X0 X1
       have i₂ := eq2984 X0 X2
       grind)
    | exact superpose eq2984 eq9657
    | (have j1 := eq2984 X0 X2
       grind)
    | exact resolve eq9657 eq2984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2984 eq9657
  have eq11278 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (τ X0) X2))) = X0 ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11199 X0 X1 X2
       have i₂ := eq64 (σ X0) X1
       grind)
    | exact superpose eq64 eq11199
    | (have j0 := eq11199 X0 X1 X2
       grind)
    | exact resolve eq11199 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq11199
  have eq15391 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (τ (σ X0)) X1)))) ∨ (M.op (σ (σ X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X0 (σ (M.op (τ (σ X0)) X1))
       have i₂ := eq11278 (σ X0) X2 X1
       grind)
    | exact superpose eq11278 eq29
    | (have j1 := eq11278 (σ X0) X2 X2
       grind)
    | exact resolve eq29 eq11278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11278
  have eq15412 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (M.op (τ (σ X0)) X1)) ∨ (M.op (σ (σ X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15391 X0 X1 X2
       have i₂ := eq10 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq10 eq15391
    | (have j0 := eq15391 X0 X1 X2
       grind)
    | exact resolve eq15391 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15391
  have eq15448 : ∀ X0 X1 X2 : G, (M.op (σ (σ X0)) X2) = X2 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15412 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15412
    | (have j0 := eq15412 X0 X1 X2
       grind)
    | exact resolve eq15412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15412
  have eq15494 : ∀ X0 X1 : G, (τ (σ (σ X0))) = (k (τ (σ (σ X0))) (σ X0)) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq117 (σ X0)
       have i₂ := eq15448 X0 X1 (σ (σ X0))
       grind)
    | exact superpose eq15448 eq117
    | (have j1 := eq15448 X0 X1 x
       grind)
    | exact resolve eq117 eq15448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq15448
  have eq15565 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15494 X0 X1
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq15494
    | (have j0 := eq15494 X0 X1
       grind)
    | exact resolve eq15494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15494
  have eq15576 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X0)) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15565 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq15565
    | (have j0 := eq15565 X0 X1
       grind)
    | exact resolve eq15565 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15565
  have eq15610 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X0) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq15576 X0 X1
       grind)
    | exact superpose eq15576 eq10
    | (have j1 := eq15576 X0 X1
       grind)
    | exact resolve eq10 eq15576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15576
  have eq15676 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15610 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15610
    | (have j0 := eq15610 X0 X1
       grind)
    | exact resolve eq15610 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15610
  have eq15699 : ∀ X0 X1 : G, (k X1 X1) = X1 ∨ (k X1 (k X0 X1)) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15676 X1 (k X0 X1)
       have i₂ := eq1205 X1 X0
       grind)
    | exact superpose eq1205 eq15676
    | (have j0 := eq15676 X1 X1
       have j1 := eq1205 (k X1 X1) X1
       grind)
    | exact resolve eq15676 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq15676
  have eq17627 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (k (k X0 X0) X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq15699 (k X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15699
  have eq17628 : ∀ X0 : G, (k X0 (k (k X0 X0) X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq17627 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17627
  have eq41064 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2321 X0 (k (k (σ X0) (σ X0)) (σ X0))
       have i₂ := eq17628 (σ X0)
       grind)
    | exact superpose eq17628 eq2321
    | (have j1 := eq17628 (σ X0)
       grind)
    | exact resolve eq2321 eq17628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321 eq17628
  have eq41271 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq41064 X0
       have j1 := eq3761 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq41064 X0
       have r₂ := eq3761 (σ X0) x
       grind)
    | exact resolve eq41064 eq3761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3761 eq41064
  have eq41379 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41271 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq41271
    | exact resolve eq41271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41271
  have eq41444 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq41379 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq41379
    | exact resolve eq41379 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41499 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1092
       have i₂ := eq41379 x
       grind)
    | exact superpose eq41379 eq1092
    | exact resolve eq1092 eq41379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq41734 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq41444 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq41444
    | exact resolve eq41444 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq41444
  have eq41812 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq41734 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq41734
    | exact resolve eq41734 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41734
  have eq46141 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41499
       have i₂ := eq41812 x
       grind)
    | exact superpose eq41812 eq41499
    | exact resolve eq41499 eq41812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41499
  have eq46152 : (σ x) = (σ y) := by grind
  clear eq46141
  have eq46159 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46152
       grind)
    | exact superpose eq46152 eq16
    | exact resolve eq16 eq46152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46160 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq46152
       grind)
    | exact superpose eq46152 eq10
    | exact resolve eq10 eq46152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46152
  have eq46271 : x = y := by
    first
    | (have i₁ := eq46160
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq46160
    | exact resolve eq46160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46160
  have eq46272 : (σ (M.op x y)) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq46159
       have i₂ := eq41379 x
       grind)
    | exact superpose eq41379 eq46159
    | exact resolve eq46159 eq41379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41379 eq46159
  have eq46279 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq46272
       have i₂ := eq41812 x
       grind)
    | exact superpose eq41812 eq46272
    | exact resolve eq46272 eq41812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41812 eq46272
  have eq46286 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq46279
       have i₂ := eq46271
       grind)
    | exact superpose eq46271 eq46279
    | exact resolve eq46279 eq46271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46271 eq46279
  have eq46287 : False := by grind
  exact eq46287

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pyx_Equation3180 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq111 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq111 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq111
    | exact resolve eq111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq406 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq413 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq406
    | (have j0 := eq406 X0 X1
       grind)
    | exact resolve eq406 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq548 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq413 x y
       grind)
    | exact superpose eq413 eq16
    | (have j1 := eq413 x y
       grind)
    | exact resolve eq16 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq12501 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq405 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq405
    | exact resolve eq405 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq12604 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12501 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq12501
    | (have j0 := eq12501 X0 X1
       grind)
    | exact resolve eq12501 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12501
  have eq14184 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq548
       have i₂ := eq12604 x y
       grind)
    | exact superpose eq12604 eq548
    | (have j1 := eq12604 x y
       grind)
    | (have r₁ := eq548
       have r₂ := eq12604 x y
       grind)
    | (have r₁ := eq548
       have r₂ := eq12604 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq548
       have r₂ := eq12604 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq548 eq12604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq12604
  have eq14185 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq14184
  have eq21800 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14185
       grind)
    | exact superpose eq14185 eq16
    | exact resolve eq16 eq14185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14185
  have eq21801 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq21800
       have r₂ := eq23 x
       grind)
    | exact resolve eq21800 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21800
  have eq21803 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21801
       grind)
    | exact superpose eq21801 eq10
    | exact resolve eq10 eq21801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21801
  have eq21882 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq21803
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21803
    | exact resolve eq21803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21803
  have eq22267 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21882
       grind)
    | exact superpose eq21882 eq16
    | exact resolve eq16 eq21882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21882
  have eq22268 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq22267
       have r₂ := eq23 x
       grind)
    | exact resolve eq22267 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22267
  have eq22303 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq22268
       grind)
    | exact superpose eq22268 eq10
    | exact resolve eq10 eq22268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22268
  have eq22383 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq22303
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22303
    | exact resolve eq22303 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22303
  have eq22384 : x = (M.op y y) := by grind
  clear eq22383
  have eq22390 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112 y
       have i₂ := eq22384
       grind)
    | exact superpose eq22384 eq112
    | exact resolve eq112 eq22384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq22513 : y = (M.op x y) := by
    first
    | (have i₁ := eq111 y y
       have i₂ := eq22384
       grind)
    | exact superpose eq22384 eq111
    | exact resolve eq111 eq22384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq22384
  have eq22676 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22390
       grind)
    | exact superpose eq22390 eq16
    | exact resolve eq16 eq22390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22390
  have eq22742 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq22676
       have i₂ := eq22513
       grind)
    | exact superpose eq22513 eq22676
    | exact resolve eq22676 eq22513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22513 eq22676
  have eq22743 : False := by grind
  exact eq22743

/-- `Equation3201`: `x = (((y ◇ z) ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pyx_y_pxy_Equation3201 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3201 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3201.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : x ≠ (M.op x y) ∨ (k x y) = (M.op y x) := by
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
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X1) X2) ≠ X0 ∨ (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = (k (M.op (M.op (M.op X1 X2) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op (M.op X1 X2) X1) X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op (M.op X1 X2) X1) X2) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op (M.op X1 X2) X1) X2) (M.op (M.op (M.op X1 X2) X1) X2)
       have r₂ := eq14 (M.op (M.op (M.op X1 X2) X1) X2) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ x = (k y x) := by
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
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq94 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq95 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq214 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op x y) x) y)) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
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
  have eq733 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq736 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq730 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq730 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq730 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq730 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq746 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq736 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq736
    | (have j0 := eq736 X0 X1
       grind)
    | exact resolve eq736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq860 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X1) (M.op (M.op (M.op X0 X1) X0) X1)) = (k (M.op (M.op (M.op X0 X1) X0) X1) (M.op (M.op (M.op X0 X1) X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65 (M.op (M.op (M.op X0 X1) X0) X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq861 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (k (M.op (M.op (M.op X0 X1) X0) X1) (M.op (M.op (M.op X0 X1) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq860 X0 X1
       have i₂ := eq14 (M.op (M.op (M.op X0 X1) X0) X1) X0 X1
       grind)
    | exact superpose eq14 eq860
    | exact resolve eq860 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq3789 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq94 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq94
    | (have j0 := eq94 x
       grind)
    | exact resolve eq94 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq3801 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3789
  have eq3806 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3801
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3801
    | exact resolve eq3801 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq3801
  have eq3824 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3806
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq3806 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3806
  have eq3831 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3824 eq49
    | exact resolve eq49 eq3824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3824
  have eq3974 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq95 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95
    | (have j0 := eq95 y
       grind)
    | exact resolve eq95 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq3985 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3974
  have eq3989 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3985
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq3985
    | exact resolve eq3985 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq3985
  have eq4014 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq3989
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq3989 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3989
  have eq4037 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4014 eq87
    | exact resolve eq87 eq4014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq4014
  have eq6730 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq733 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq733
    | (have j0 := eq733 x y
       grind)
    | exact resolve eq733 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq6799 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6730
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6730
    | exact resolve eq6730 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6730
  have eq6886 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6799
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6799
    | exact resolve eq6799 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6799
  have eq6973 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6886
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6886
    | exact resolve eq6886 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6886
  have eq7057 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq6973
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6973
    | exact resolve eq6973 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6973
  have eq7139 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq7057
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7057
    | exact resolve eq7057 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7057
  have eq7199 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq7139
    | exact resolve eq7139 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7139
  have eq15050 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15057 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq15050
    | exact resolve eq15050 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15050
  have eq15068 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq15057
       have r₂ := eq27
       grind)
    | exact resolve eq15057 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15057
  have eq15070 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq15068
    | exact resolve eq15068 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15068
  have eq15072 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15070 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15070
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15070
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15070
       grind)
    | exact resolve eq12 eq15070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15070
  have eq15085 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq15072
  have eq15087 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq15085
    | exact resolve eq15085 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15085
  have eq15088 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq15087
  have eq16618 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15088 eq57
    | exact resolve eq57 eq15088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq16619 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15088 eq116
    | exact resolve eq116 eq15088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15088
  have eq16635 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16619
  have eq16643 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq16618
    | exact resolve eq16618 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16618
  have eq16646 : y ≠ y ∨ x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq16635
       grind)
    | exact superpose eq16635 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq16635
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq16635
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16635
       grind)
    | exact resolve eq12 eq16635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16647 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq16635
       grind)
    | exact superpose eq16635 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16635
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16635
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq16635
       grind)
    | exact resolve eq13 eq16635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16635
  have eq16658 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16647
  have eq16659 : x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16646
  have eq16660 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16658
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16658
    | exact resolve eq16658 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16658
  have eq16661 : x = (M.op x y) ∨ y = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16659
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16659
    | exact resolve eq16659 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16659
  have eq16662 : y = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16661
  have eq16874 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq16660
       grind)
    | exact superpose eq16660 eq72
    | exact resolve eq72 eq16660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16660
  have eq16902 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq16874
    | exact resolve eq16874 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16874
  have eq16950 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq16662
       grind)
    | exact superpose eq16662 eq44
    | exact resolve eq44 eq16662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16662
  have eq16979 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16950
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16950
    | exact resolve eq16950 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16950
  have eq17213 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16979 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq16979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16979
  have eq17224 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq17213
    | exact resolve eq17213 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17213
  have eq17235 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq17224
    | exact resolve eq17224 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17224
  have eq17236 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq17235
  have eq17247 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq16643
       grind)
    | exact superpose eq16643 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq16643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16643
  have eq17256 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17247
  have eq17265 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17256
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17256
    | exact resolve eq17256 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17256
  have eq17281 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17265
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17265
    | exact resolve eq17265 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17265
  have eq17282 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17281
  have eq17446 : y ≠ y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq17282
       grind)
    | exact superpose eq17282 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq17282
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17282
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq17282
       grind)
    | exact resolve eq13 eq17282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17282
  have eq17458 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17446
  have eq17460 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17458
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17458
    | exact resolve eq17458 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17458
  have eq17475 : (σ y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq746 y x
       have i₂ := eq17460
       grind)
    | exact superpose eq17460 eq746
    | (have j0 := eq746 y x
       grind)
    | exact resolve eq746 eq17460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17460
  have eq17482 : (σ y) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17475
    | exact resolve eq17475 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17475
  have eq17496 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17482
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17482
    | exact resolve eq17482 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17482
  have eq17505 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17496
    | exact resolve eq17496 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17496
  have eq17512 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17505
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17505
    | exact resolve eq17505 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17505
  have eq17519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17512
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17512
    | exact resolve eq17512 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17512
  have eq17527 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq17519
    | exact resolve eq17519 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17519
  have eq17536 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17527
       have r₂ := eq27
       grind)
    | exact resolve eq17527 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17527
  have eq17544 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17536
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17536
    | exact resolve eq17536 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17536
  have eq17550 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17544
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17544
    | exact resolve eq17544 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17544
  have eq17553 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq17550
    | exact resolve eq17550 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17550
  have eq17554 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17553
  have eq18116 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq17236 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq17236
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq17236
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17236
       grind)
    | exact resolve eq13 eq17236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17236
  have eq18128 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq18116
  have eq18130 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq18128
    | exact resolve eq18128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18128
  have eq18161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18130 eq16902
    | exact resolve eq16902 eq18130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16902 eq18130
  have eq18172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18161
  have eq18176 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18172
       have r₂ := eq27
       grind)
    | exact resolve eq18172 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18172
  have eq18183 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18176 eq51
    | exact resolve eq51 eq18176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18176
  have eq22218 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18183 eq14
    | exact resolve eq14 eq18183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18183
  have eq22313 : (τ (σ x)) = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22218 eq3831
    | exact resolve eq3831 eq22218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3831 eq22218
  have eq22383 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq22313
    | exact resolve eq22313 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22313
  have eq22412 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq22383
       grind)
    | exact superpose eq22383 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq22383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22383
  have eq22427 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22412
  have eq22462 : ∀ X0 : G, (M.op (M.op (M.op x x) x) X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq22427
       grind)
    | exact superpose eq22427 eq14
    | exact resolve eq14 eq22427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22427
  have eq27533 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq22462 x
       grind)
    | exact superpose eq22462 eq14
    | exact resolve eq14 eq22462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22462
  have eq27831 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq27533 y
       grind)
    | exact superpose eq27533 eq18
    | (have j1 := eq27533 y
       grind)
    | exact resolve eq18 eq27533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27533
  have eq27899 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27831
       have r₂ := eq17554
       grind)
    | exact resolve eq27831 eq17554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17554 eq27831
  have eq27919 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27899 eq27
    | exact resolve eq27 eq27899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27921 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27899 eq64
    | (have r₁ := eq64
       have r₂ := eq27899
       grind)
    | exact resolve eq64 eq27899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq27922 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27899 eq76
    | (have r₁ := eq76
       have r₂ := eq27899
       grind)
    | exact resolve eq76 eq27899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq27929 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq27922
  have eq27930 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq27921
  have eq27942 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27930 eq116
    | exact resolve eq116 eq27930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq27930
  have eq27988 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq27942
  have eq28354 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27929 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq27929
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq27929
       grind)
    | exact resolve eq13 eq27929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27929
  have eq28366 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq28354
  have eq28373 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq28366
    | exact resolve eq28366 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28366
  have eq28455 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq28373
  have eq28472 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq28455
       have r₂ := eq27899
       grind)
    | exact resolve eq28455 eq27899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27899 eq28455
  have eq28484 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28472 eq82
    | exact resolve eq82 eq28472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq28472
  have eq28550 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq28484
    | exact resolve eq28484 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq28484
  have eq28584 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq28550
       grind)
    | exact superpose eq28550 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq28550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28618 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28584
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28584
    | exact resolve eq28584 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28584
  have eq28619 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq28618
  have eq29507 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq28619
       grind)
    | exact superpose eq28619 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq28619
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq28619
       grind)
    | exact resolve eq13 eq28619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28619
  have eq29520 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq29507
  have eq29523 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29520
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29520
    | exact resolve eq29520 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29520
  have eq29545 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28550
       have i₂ := eq29523
       grind)
    | exact superpose eq29523 eq28550
    | exact resolve eq28550 eq29523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29523
  have eq29554 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq29545
  have eq29639 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq29554
       grind)
    | exact superpose eq29554 eq14
    | exact resolve eq14 eq29554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29554
  have eq29667 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq29639 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29639
    | (have j0 := eq29639 X0
       grind)
    | exact resolve eq29639 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29639
  have eq29694 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X0) X1) = X1 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq29667 eq214
    | exact resolve eq214 eq29667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq29667
  have eq29966 : y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq861 x y
       have i₂ := eq29694 x y
       grind)
    | exact superpose eq29694 eq861
    | exact resolve eq861 eq29694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29694
  have eq30125 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq746 y y
       have i₂ := eq29966
       grind)
    | exact superpose eq29966 eq746
    | (have j0 := eq746 y y
       grind)
    | exact resolve eq746 eq29966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29966
  have eq30130 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq30125
  have eq30131 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq30130
  have eq30142 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30131
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30131
    | exact resolve eq30131 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30131
  have eq30182 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ y)) (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30142 eq14
    | exact resolve eq14 eq30142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30142
  have eq31689 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30182 eq14
    | exact resolve eq14 eq30182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30182
  have eq31797 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31689 eq27988
    | exact resolve eq27988 eq31689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27988 eq31689
  have eq31856 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq31797
  have eq31903 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq31856
       have r₂ := eq27919
       grind)
    | exact resolve eq31856 eq27919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27919 eq31856
  have eq31927 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq31903
       grind)
    | exact superpose eq31903 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq31903
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq31903
       grind)
    | exact resolve eq13 eq31903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31903
  have eq31939 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq31927
  have eq31946 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq31939
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31939
    | exact resolve eq31939 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31939
  have eq33189 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28550
       have i₂ := eq31946
       grind)
    | exact superpose eq31946 eq28550
    | exact resolve eq28550 eq31946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28550 eq31946
  have eq33198 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq33189
  have eq33274 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33198 eq20
    | exact resolve eq20 eq33198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33276 : ∀ X0 : G, (M.op (M.op (M.op y x) y) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33198 eq50
    | exact resolve eq50 eq33198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq33198
  have eq33414 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33274
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33274
    | exact resolve eq33274 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33274
  have eq33676 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33414 eq26
    | exact resolve eq26 eq33414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33414
  have eq37663 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq861 y x
       have i₂ := eq33276 x
       grind)
    | exact superpose eq33276 eq861
    | exact resolve eq861 eq33276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq33276
  have eq37864 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq746 x x
       have i₂ := eq37663
       grind)
    | exact superpose eq37663 eq746
    | (have j0 := eq746 x x
       grind)
    | exact resolve eq746 eq37663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37663
  have eq37869 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq37864
  have eq37870 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq37869
  have eq37885 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37870
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37870
    | exact resolve eq37870 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37870
  have eq37938 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37885 eq14
    | exact resolve eq14 eq37885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37885
  have eq42808 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f42808_13 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X0) = X0 ∨ x = (M.op x y) := by
      intro X0
      grind
    have f42808_19 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
      intro X0 X1 X2
      grind
    have f42808_21 : X0 ≠ (M.op (σ x) X0) := by grind
    have f42808_22 : x ≠ (M.op x y) := by grind
    have f42808_23 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X0) = X0 := by
      intro X0
      first
      | (have j0 := f42808_13 X0
         grind)
      | (have r₁ := f42808_13 X0
         have r₂ := f42808_22
         grind)
      | exact resolve f42808_13 f42808_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f42808_28 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
      intro X0
      first
      | (have i₁ := f42808_19 X0 (σ x) (σ x)
         have i₂ := f42808_23 (σ x)
         grind)
      | exact superpose f42808_23 f42808_19
      | exact resolve f42808_19 f42808_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f42808_31 : X0 ≠ X0 := by
      first
      | (have i₁ := f42808_21
         have i₂ := f42808_28 X0
         grind)
      | exact superpose f42808_28 f42808_21
      | (have r₁ := f42808_21
         have r₂ := f42808_28 X0
         grind)
      | exact resolve f42808_21 f42808_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f42808_36 : False := by grind
    exact f42808_36
  clear eq37938
  have eq42919 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42808 eq33676
    | exact resolve eq33676 eq42808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33676 eq42808
  have eq43003 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq42919
  have eq43042 : x = (M.op x y) := by
    first
    | (have r₁ := eq43003
       have r₂ := eq27
       grind)
    | exact resolve eq43003 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43003
  have eq43061 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq43042 eq20
    | exact resolve eq20 eq43042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq43065 : x ≠ x ∨ (k x y) = (M.op y x) := by
    first
    | exact superpose eq43042 eq63
    | (have r₁ := eq63
       have r₂ := eq43042
       grind)
    | exact resolve eq63 eq43042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq43068 : x ≠ x ∨ y = (M.op y x) ∨ x = (k y x) := by
    first
    | exact superpose eq43042 eq75
    | (have r₁ := eq75
       have r₂ := eq43042
       grind)
    | exact resolve eq75 eq43042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq43133 : y = (M.op y x) ∨ x = (k y x) := by grind
  clear eq43068
  have eq43134 : (k x y) = (M.op y x) := by grind
  clear eq43065
  have eq43196 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq43061
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43061
    | exact resolve eq43061 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43061
  have eq43233 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq43196 eq26
    | exact resolve eq26 eq43196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43238 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq43196 eq51
    | exact resolve eq51 eq43196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq43319 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43196 eq7199
    | exact resolve eq7199 eq43196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7199
  have eq43417 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq43319
       have r₂ := eq27
       grind)
    | exact resolve eq43319 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43319
  have eq43521 : (k (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq43134
       grind)
    | exact superpose eq43134 eq44
    | exact resolve eq44 eq43134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq43134
  have eq43573 : (σ (M.op y x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq43196 eq43521
    | exact resolve eq43521 eq43196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43521
  have eq44068 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq43133
       grind)
    | exact superpose eq43133 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq43133
       grind)
    | exact resolve eq13 eq43133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43133
  have eq44080 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq44068
  have eq44082 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq44080
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq44080
    | exact resolve eq44080 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq44080
  have eq44085 : x = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq43042 eq44082
    | exact resolve eq44082 eq43042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43042 eq44082
  have eq44086 : x = (k y x) := by grind
  clear eq44085
  have eq44093 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq44086
       grind)
    | exact superpose eq44086 eq72
    | exact resolve eq72 eq44086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq44124 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq746 y x
       have i₂ := eq44086
       grind)
    | exact superpose eq44086 eq746
    | (have j0 := eq746 y x
       grind)
    | exact resolve eq746 eq44086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746 eq44086
  have eq44128 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq44124
  have eq44140 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44128
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44128
    | exact resolve eq44128 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44128
  have eq44153 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq43196 eq44093
    | exact resolve eq44093 eq43196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44093
  have eq44158 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44140
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44140
    | exact resolve eq44140 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44140
  have eq44170 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq44153
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44153
    | exact resolve eq44153 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44153
  have eq44174 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43196 eq44158
    | exact resolve eq44158 eq43196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44158
  have eq44186 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq43196 eq44170
    | exact resolve eq44170 eq43196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44170
  have eq44190 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq44174
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44174
    | exact resolve eq44174 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq44174
  have eq44200 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq44190
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44190
    | exact resolve eq44190 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44190
  have eq44207 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq26 eq44200
    | exact resolve eq44200 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq44200
  have eq44214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq43196 eq44207
    | exact resolve eq44207 eq43196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44207
  have eq44221 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have r₁ := eq44214
       have r₂ := eq27
       grind)
    | exact resolve eq44214 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44214
  have eq44291 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq44186 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq44186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq43233 eq44291
    | exact resolve eq44291 eq43233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44291
  have eq44312 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq44301
       have r₂ := eq27
       grind)
    | exact resolve eq44301 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44301
  have eq44753 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq44312 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ y) (σ (M.op x y))
       have r₂ := eq44312
       grind)
    | exact resolve eq13 eq44312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44312
  have eq44766 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq44753
  have eq44770 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq43233 eq44766
    | exact resolve eq44766 eq43233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44766
  have eq44772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq44186 eq44770
    | exact resolve eq44770 eq44186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44186 eq44770
  have eq44774 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq44772
       have r₂ := eq27
       grind)
    | exact resolve eq44772 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq44772
  have eq44780 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq44774 eq14
    | exact resolve eq14 eq44774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44801 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq43233 eq44780
    | exact resolve eq44780 eq43233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43233 eq44780
  have eq44825 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq44801 eq43238
    | exact resolve eq43238 eq44801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43238 eq44801
  have eq44932 : (τ (σ y)) = (k y y) := by
    first
    | exact superpose eq44825 eq4037
    | exact resolve eq4037 eq44825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4037 eq44825
  have eq45013 : y = (k y y) := by
    first
    | exact superpose eq29 eq44932
    | exact resolve eq44932 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq44932
  have eq45051 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq45013
       grind)
    | exact superpose eq45013 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq45013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45013
  have eq45066 : y = (M.op y y) := by grind
  clear eq45051
  have eq45123 : ∀ X0 : G, (M.op (M.op (M.op y y) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq45066
       grind)
    | exact superpose eq45066 eq14
    | exact resolve eq14 eq45066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45145 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq45123 X0
       have i₂ := eq45066
       grind)
    | exact superpose eq45066 eq45123
    | exact resolve eq45123 eq45066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45123
  have eq45156 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq45145 X0
       have i₂ := eq45066
       grind)
    | exact superpose eq45066 eq45145
    | exact resolve eq45145 eq45066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45066 eq45145
  have eq45191 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq43573
       have i₂ := eq45156 x
       grind)
    | exact superpose eq45156 eq43573
    | exact resolve eq43573 eq45156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43573 eq45156
  have eq45260 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq45191
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45191
    | exact resolve eq45191 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45191
  have eq45272 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq43196 eq45260
    | exact resolve eq45260 eq43196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43196 eq45260
  have eq46103 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq45272 eq43417
    | (have r₁ := eq43417
       have r₂ := eq45272
       grind)
    | exact resolve eq43417 eq45272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43417 eq45272
  have eq46124 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq46103
  have eq46131 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq44774 eq46124
    | exact resolve eq46124 eq44774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44774 eq46124
  have eq46145 : False := by grind
  exact eq46145
