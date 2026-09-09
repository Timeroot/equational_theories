import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_y_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq56 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq84
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86
    | exact resolve eq86 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
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
  have eq517 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq524 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq517 X0
       grind)
    | exact superpose eq517 eq14
    | exact resolve eq14 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1005 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq524
    | exact resolve eq524 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1007 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51 eq524
    | exact resolve eq524 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq524
  have eq9132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9133 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq9132
    | exact resolve eq9132 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9132
  have eq9144 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq9133
       have r₂ := eq28
       grind)
    | exact resolve eq9133 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9133
  have eq9146 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq9144
    | exact resolve eq9144 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9144
  have eq9150 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq9146 eq517
    | exact resolve eq517 eq9146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9151 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq9146
  have eq9179 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq9150
    | exact resolve eq9150 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9150
  have eq9183 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9179
  have eq9654 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq9183
       grind)
    | exact superpose eq9183 eq45
    | exact resolve eq45 eq9183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq9183
  have eq9668 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9654
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq9654
    | exact resolve eq9654 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9654
  have eq9712 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9668 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq9668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9668
  have eq9715 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq9712
    | exact resolve eq9712 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9712
  have eq9716 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9715
  have eq9728 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq9716
    | exact resolve eq9716 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9716
  have eq9729 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9728
  have eq9940 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9729 eq517
    | exact resolve eq517 eq9729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9729
  have eq9975 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq9940
    | exact resolve eq9940 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9940
  have eq9976 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9975
  have eq9977 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9976 eq28
    | exact resolve eq28 eq9976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9976
  have eq10926 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq9151 eq87
    | exact resolve eq87 eq9151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq9151
  have eq10935 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10926
  have eq10943 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10935
       have r₂ := eq9977
       grind)
    | exact resolve eq10935 eq9977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10935
  have eq10956 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq517 y
       have i₂ := eq10943
       grind)
    | exact superpose eq10943 eq517
    | exact resolve eq517 eq10943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq10943
  have eq10993 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10956
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10956
    | exact resolve eq10956 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10956
  have eq11022 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10993 eq1007
    | exact resolve eq1007 eq10993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10993
  have eq11125 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq11022
  have eq11981 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11125 eq56
    | exact resolve eq56 eq11125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq11125
  have eq12015 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq11981
    | exact resolve eq11981 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11981
  have eq12035 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq12015
       grind)
    | exact superpose eq12015 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq12015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12015
  have eq12036 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12035
  have eq12059 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq12036
       grind)
    | exact superpose eq12036 eq47
    | exact resolve eq47 eq12036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12060 : x = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq12036
       grind)
    | exact superpose eq12036 eq50
    | exact resolve eq50 eq12036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq12036
  have eq12136 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1005 eq12060
    | exact resolve eq12060 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12060
  have eq20642 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12136 eq12059
    | exact resolve eq12059 eq12136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12059 eq12136
  have eq20682 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20642
  have eq20684 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20682
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20682
    | exact resolve eq20682 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20682
  have eq20685 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq20684
  have eq20686 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20685 eq21
    | exact resolve eq21 eq20685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20685
  have eq20825 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20686
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20686
    | exact resolve eq20686 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20686
  have eq20906 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20825 eq9977
    | (have r₁ := eq9977
       have r₂ := eq20825
       grind)
    | exact resolve eq9977 eq20825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9977
  have eq20942 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20906
  have eq20943 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20942
  have eq21010 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20943 eq216
    | exact resolve eq216 eq20943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq21037 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20943 eq1007
    | exact resolve eq1007 eq20943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq20943
  have eq27401 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21037 eq21010
    | exact resolve eq21010 eq21037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21010 eq21037
  have eq27465 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27401
  have eq27469 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq27465
    | exact resolve eq27465 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27465
  have eq27474 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27469 eq28
    | exact resolve eq28 eq27469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27469
  have eq27547 : x = (M.op x y) := by
    first
    | (have r₁ := eq27474
       have r₂ := eq20825
       grind)
    | exact resolve eq27474 eq20825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20825 eq27474
  have eq27551 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq27547 eq21
    | exact resolve eq21 eq27547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq27632 : x = (M.op x x) := by
    first
    | exact superpose eq27547 eq1005
    | exact resolve eq1005 eq27547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq27701 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq27551
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27551
    | exact resolve eq27551 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27551
  have eq27713 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq27701 eq27
    | exact resolve eq27 eq27701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq27888 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq27632
       grind)
    | exact superpose eq27632 eq47
    | exact resolve eq47 eq27632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq27912 : x = (k x x) := by grind
  have eq27997 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq27547 eq27888
    | exact resolve eq27888 eq27547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27888
  have eq28019 : y = (M.op x y) := by
    first
    | (have i₁ := eq27997
       have i₂ := eq27632
       grind)
    | exact superpose eq27632 eq27997
    | exact resolve eq27997 eq27632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27632 eq27997
  have eq28031 : y = (M.op x y) := by
    first
    | (have i₁ := eq28019
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28019
    | exact resolve eq28019 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq28019
  have eq28036 : x = y := by
    first
    | exact superpose eq27547 eq28031
    | exact resolve eq28031 eq27547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27547 eq28031
  have eq28046 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq28036
       grind)
    | exact superpose eq28036 eq25
    | exact resolve eq25 eq28036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq28036
  have eq28204 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq28046
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28046
    | exact resolve eq28046 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28046
  have eq28268 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27701 eq28204
    | exact resolve eq28204 eq27701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28204
  have eq28534 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28268 eq27713
    | exact resolve eq27713 eq28268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27713 eq28268
  have eq28615 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq707 x x
       have i₂ := eq27912
       grind)
    | exact superpose eq27912 eq707
    | (have j0 := eq707 x x
       grind)
    | exact resolve eq707 eq27912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq27912
  have eq28620 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq28615
  have eq28621 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq28620
  have eq28636 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq28621
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28621
    | exact resolve eq28621 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq28621
  have eq28654 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27701 eq28636
    | exact resolve eq28636 eq27701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27701 eq28636
  have eq28762 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28534 eq28654
    | exact resolve eq28654 eq28534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28534 eq28654
  have eq28763 : False := by grind
  exact eq28763

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_y_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq68 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq45
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq76
    | exact resolve eq76 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq82
    | exact resolve eq82 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq371 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq50 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq522 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq66 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq8263 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq83 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8264 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq8263
    | exact resolve eq8263 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8263
  have eq8275 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq8264
       have r₂ := eq29
       grind)
    | exact resolve eq8264 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8264
  have eq8430 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq8275 eq371
    | exact resolve eq371 eq8275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8431 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq8275
  have eq8448 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq8430
    | exact resolve eq8430 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8430
  have eq8452 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8448
  have eq8678 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq8452
       grind)
    | exact superpose eq8452 eq46
    | exact resolve eq46 eq8452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq8452
  have eq8694 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8678
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq8678
    | exact resolve eq8678 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8678
  have eq8910 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8694 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq8694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8694
  have eq8911 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8910
  have eq8915 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq8911
    | exact resolve eq8911 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8911
  have eq8916 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq8915
  have eq8930 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq8916 eq371
    | exact resolve eq371 eq8916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8916
  have eq8952 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq8930
    | exact resolve eq8930 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8930
  have eq8953 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8952
  have eq8954 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8953 eq29
    | exact resolve eq29 eq8953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8953
  have eq9688 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq8431 eq83
    | exact resolve eq83 eq8431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq8431
  have eq9697 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq9688
  have eq9706 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9697
       have r₂ := eq8954
       grind)
    | exact resolve eq9697 eq8954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9697
  have eq9925 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq371 y
       have i₂ := eq9706
       grind)
    | exact superpose eq9706 eq371
    | exact resolve eq371 eq9706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq9706
  have eq9955 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9925
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq9925
    | exact resolve eq9925 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9925
  have eq9957 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq9955 eq31
    | exact resolve eq31 eq9955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq9955
  have eq10077 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq9957
    | exact resolve eq9957 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9957
  have eq10078 : y = (M.op x y) ∨ x = y := by grind
  clear eq10077
  have eq10079 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq10078 eq22
    | exact resolve eq22 eq10078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10207 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10079
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10079
    | exact resolve eq10079 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10079
  have eq10510 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq10207 eq8954
    | (have r₁ := eq8954
       have r₂ := eq10207
       grind)
    | exact resolve eq8954 eq10207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8954 eq10207
  have eq10519 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq10510
  have eq10520 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq10519
  have eq10580 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq10520 eq30
    | exact resolve eq30 eq10520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10520
  have eq10707 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq10580
    | exact resolve eq10580 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq10580
  have eq10786 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq10707 eq10078
    | exact resolve eq10078 eq10707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10078 eq10707
  have eq10787 : x = y := by grind
  clear eq10786
  have eq11072 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq10787
       grind)
    | exact superpose eq10787 eq20
    | exact resolve eq20 eq10787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq11073 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq10787
       grind)
    | exact superpose eq10787 eq26
    | exact resolve eq26 eq10787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq10787
  have eq11194 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11073
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11073
    | exact resolve eq11073 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11073
  have eq11196 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11194 eq28
    | exact resolve eq28 eq11194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq11194
  have eq11637 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq11072
       grind)
    | exact superpose eq11072 eq68
    | exact resolve eq68 eq11072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq11656 : x = (k (M.op x y) x) := by grind
  clear eq11072
  have eq11694 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq11637
    | exact resolve eq11637 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11637
  have eq11750 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq20346 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq20358 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11196 eq20346
    | exact resolve eq20346 eq11196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20346
  have eq20370 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20358
       have r₂ := eq29
       grind)
    | exact resolve eq20358 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20358
  have eq20375 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11196 eq20370
    | exact resolve eq20370 eq11196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20370
  have eq20381 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20375 eq29
    | exact resolve eq29 eq20375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20412 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20375 eq11750
    | exact resolve eq11750 eq20375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11750 eq20375
  have eq22188 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20412 eq11694
    | exact resolve eq11694 eq20412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11694 eq20412
  have eq22203 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq22188
  have eq22214 : x = (M.op x y) := by
    first
    | (have r₁ := eq22203
       have r₂ := eq20381
       grind)
    | exact resolve eq22203 eq20381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20381 eq22203
  have eq23877 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq22214 eq22
    | exact resolve eq22 eq22214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq23957 : x = (k x x) := by
    first
    | exact superpose eq22214 eq11656
    | exact resolve eq11656 eq22214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11656 eq22214
  have eq24029 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq23877
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23877
    | exact resolve eq23877 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23877
  have eq24922 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq522 x
       have i₂ := eq23957
       grind)
    | exact superpose eq23957 eq522
    | (have j0 := eq522 x
       grind)
    | exact resolve eq522 eq23957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq23957
  have eq24927 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq24922
  have eq24934 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq24927
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24927
    | exact resolve eq24927 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq24927
  have eq24951 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11196 eq24934
    | exact resolve eq24934 eq11196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11196 eq24934
  have eq24966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24029 eq24951
    | exact resolve eq24951 eq24029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24029 eq24951
  have eq24981 : False := by grind
  exact eq24981

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pxy_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
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
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X1
       have i₂ := eq174 (M.op X0 X1)
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 : G, (M.op (M.op (k X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq181 X0 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq181
    | exact resolve eq181 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq586 : ∀ X0 : G, (M.op (k (k X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq567 X0
       have i₂ := eq174 (k X0 X0)
       grind)
    | exact superpose eq174 eq567
    | exact resolve eq567 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq623 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq183 (k (M.op X0 x) (M.op X0 x)) x
       have i₂ := eq183 X0 x
       grind)
    | exact superpose eq183 eq183
    | exact resolve eq183 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq633 : ∀ X0 : G, (k X0 X0) = (M.op (M.op (k (k X0 X0) (k X0 X0)) X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq182 (k X0 X0) X0
       have i₂ := eq623 X0
       grind)
    | exact superpose eq623 eq182
    | exact resolve eq182 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq623
  have eq637 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq633 X0
       have i₂ := eq586 X0
       grind)
    | exact superpose eq586 eq633
    | exact resolve eq633 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq633
  have eq638 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq637 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq637
    | exact resolve eq637 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq759 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq759
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq759
    | exact resolve eq759 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq774 : (M.op x y) = (k x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq754
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq754
    | exact resolve eq754 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq1496 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq774
       grind)
    | exact superpose eq774 eq40
    | exact resolve eq40 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq774
  have eq1497 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1496
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1496
    | exact resolve eq1496 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq1499 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq1497
    | exact resolve eq1497 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq2419 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq1499 eq769
    | exact resolve eq769 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq1499
  have eq2426 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq2419
       have r₂ := eq27
       grind)
    | exact resolve eq2419 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419
  have eq2434 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq2426 eq97
    | exact resolve eq97 eq2426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq2426
  have eq2457 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq2434
    | exact resolve eq2434 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2434
  have eq2458 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2457
  have eq2479 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq637 x
       have i₂ := eq2458
       grind)
    | exact superpose eq2458 eq637
    | exact resolve eq637 eq2458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq2480 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq638 x
       have i₂ := eq2458
       grind)
    | exact superpose eq2458 eq638
    | exact resolve eq638 eq2458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638 eq2458
  have eq2486 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2480
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2480
    | exact resolve eq2480 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480
  have eq2487 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2479
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2479
    | exact resolve eq2479 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq2491 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2486
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2486
    | exact resolve eq2486 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486
  have eq2495 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq2491
    | exact resolve eq2491 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491
  have eq2618 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2487 eq31
    | exact resolve eq31 eq2487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2487
  have eq2661 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2618
    | exact resolve eq2618 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2618
  have eq2662 : y = (M.op x y) ∨ x = y := by grind
  clear eq2661
  have eq2666 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq2662
       grind)
    | exact superpose eq2662 eq24
    | exact resolve eq24 eq2662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2662
  have eq2698 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq2666
    | exact resolve eq2666 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2666
  have eq2763 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2495 eq27
    | exact resolve eq27 eq2495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2495
  have eq2804 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2763
       have r₂ := eq2698
       grind)
    | exact resolve eq2763 eq2698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2698 eq2763
  have eq2811 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2804 eq31
    | exact resolve eq31 eq2804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2804
  have eq2860 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq2811
    | exact resolve eq2811 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2811
  have eq2861 : x = y := by grind
  clear eq2860
  have eq2878 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2861
       grind)
    | exact superpose eq2861 eq18
    | exact resolve eq18 eq2861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2879 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2861
       grind)
    | exact superpose eq2861 eq24
    | exact resolve eq24 eq2861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2861
  have eq2905 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2879
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2879
    | exact resolve eq2879 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2879
  have eq2906 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq2878
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq2878
    | exact resolve eq2878 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2878
  have eq2908 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2905 eq26
    | exact resolve eq26 eq2905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2905
  have eq2955 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2908
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq2908
    | exact resolve eq2908 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq2908
  have eq2982 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq2906
       grind)
    | exact superpose eq2906 eq39
    | exact resolve eq39 eq2906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq2906
  have eq2999 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2982
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2982
    | exact resolve eq2982 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2982
  have eq3007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2955 eq2999
    | exact resolve eq2999 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955 eq2999
  have eq3010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3007
    | exact resolve eq3007 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3007
  have eq3012 : False := by grind
  exact eq3012

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_y_pxy_Equation2712 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq45
  have eq49 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq52 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq49
  have eq53 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq52
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq16
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq50
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq50
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq78
    | exact resolve eq78 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq22 eq84
    | exact resolve eq84 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq91
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq95
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq16
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq565 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq568 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq565 (σ X0)
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq565
    | exact resolve eq565 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq8933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq85 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq8934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq28 eq8933
    | exact resolve eq8933 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8933
  have eq8945 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq8934
       have r₂ := eq29
       grind)
    | exact resolve eq8934 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8934
  have eq8949 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq8945 eq127
    | exact resolve eq127 eq8945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq8945
  have eq8999 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq8949
    | exact resolve eq8949 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8949
  have eq9000 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8999
  have eq9037 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq565 y
       have i₂ := eq9000
       grind)
    | exact superpose eq9000 eq565
    | exact resolve eq565 eq9000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq9038 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq568 y
       have i₂ := eq9000
       grind)
    | exact superpose eq9000 eq568
    | exact resolve eq568 eq9000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq9000
  have eq9051 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9038
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq9038
    | exact resolve eq9038 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9038
  have eq9052 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq9037
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq9037
    | exact resolve eq9037 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9037
  have eq9067 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9051
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9051
    | exact resolve eq9051 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9051
  have eq9074 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq9067
    | exact resolve eq9067 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9067
  have eq9218 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq9052 eq31
    | exact resolve eq31 eq9052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9052
  have eq9338 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq9218
    | exact resolve eq9218 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9218
  have eq9339 : y = (M.op x y) ∨ x = y := by grind
  clear eq9338
  have eq9356 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq9339 eq22
    | exact resolve eq22 eq9339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9339
  have eq9484 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9356
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq9356
    | exact resolve eq9356 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9356
  have eq9669 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9074 eq29
    | exact resolve eq29 eq9074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9074
  have eq9696 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq9669
       have r₂ := eq9484
       grind)
    | exact resolve eq9669 eq9484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9484 eq9669
  have eq9699 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq9696 eq31
    | exact resolve eq31 eq9696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq9696
  have eq9822 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq9699
    | exact resolve eq9699 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq9699
  have eq9823 : x = y := by grind
  clear eq9822
  have eq9841 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq9823
       grind)
    | exact superpose eq9823 eq20
    | exact resolve eq20 eq9823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq9842 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq9823
       grind)
    | exact superpose eq9823 eq26
    | exact resolve eq26 eq9823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq9823
  have eq9963 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq9842
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9842
    | exact resolve eq9842 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq9842
  have eq9979 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9963 eq28
    | exact resolve eq28 eq9963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9963
  have eq10248 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq9979 eq71
    | exact resolve eq71 eq9979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq9979
  have eq10317 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10248
       have i₂ := eq9841
       grind)
    | exact superpose eq9841 eq10248
    | exact resolve eq10248 eq9841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9841 eq10248
  have eq10327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10317 eq15
    | exact resolve eq15 eq10317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10317
  have eq10371 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq10327
    | exact resolve eq10327 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10327
  have eq10380 : False := by grind
  exact eq10380

/-- `Equation3634`: `x ◇ y = z ◇ ((w ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = Y then m(Y,X) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_x_pyx_pyy_Equation3634 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) Law3634 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3634.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq45 : ∀ X0 X1 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 X0) X4)) = (M.op X5 (M.op X0 X4)) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) X4) X5 x
       have i₂ := eq9 X0 X4 (M.op x X3) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X4 X5 : G, (M.op X0 X4) = (M.op X5 (M.op X0 X4)) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq45 X0 x x X4 X5
       have i₂ := eq9 X0 X4 x x
       grind)
    | exact superpose eq9 eq45
    | exact resolve eq45 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq51 : ∀ X0 X1 X3 : G, (M.op X0 X3) = (M.op (M.op X1 X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq47 (M.op X1 X0) X3 x
       have i₂ := eq9 X0 X3 x X1
       grind)
    | exact superpose eq9 eq47
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X1) X2
       have i₂ := eq47 X0 X1 X2
       grind)
    | exact superpose eq47 eq12
    | (have j0 := eq12 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq12 (M.op X0 x) (M.op X0 x)
       have r₂ := eq47 X0 x (M.op X0 x)
       grind)
    | exact resolve eq12 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X0 X2) ∨ (k X2 (M.op X1 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X1 X0)
       have i₂ := eq51 X0 X1 X2
       grind)
    | exact superpose eq51 eq12
    | (have j0 := eq12 X2 (M.op X1 X0)
       grind)
    | (have r₁ := eq12 x (M.op x x)
       have r₂ := eq51 x x x
       grind)
    | exact resolve eq12 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq57 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op X0 X0) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq23
    | exact resolve eq23 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq72 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq70 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq91 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X1)
       have i₂ := eq47 X0 X1 X2
       grind)
    | exact superpose eq47 eq13
    | (have j0 := eq13 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 x (M.op X0 x)
       have r₂ := eq47 X0 x x
       grind)
    | exact resolve eq13 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ X2 ∨ (M.op X2 (M.op X1 X0)) = X2 ∨ (M.op X2 (M.op X1 X0)) = (k (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X0) X2
       have i₂ := eq51 X0 X1 X2
       grind)
    | exact superpose eq51 eq13
    | (have j0 := eq13 (M.op X1 X0) X2
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq91 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq94 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X2 ∨ (M.op X0 X2) ≠ X2 ∨ (M.op X2 (M.op X1 X0)) = (k (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 X0 X1 X2
       have i₂ := eq47 X1 X0 X2
       grind)
    | (have i₁ := eq92 X0 X1 X0
       have i₂ := eq47 X0 (M.op X1 X0) x
       grind)
    | exact superpose eq47 eq92
    | (have j0 := eq92 X0 X1 X2
       grind)
    | (have r₁ := eq92 x X1 (M.op X0 x)
       have r₂ := eq47 X0 x x
       grind)
    | exact resolve eq92 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq95 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 X2) ∨ (M.op (M.op X0 X1) X2) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 X0 X1 X2
       have i₂ := eq51 X1 X0 X2
       grind)
    | exact superpose eq51 eq93
    | (have j0 := eq93 X0 X1 X2
       grind)
    | exact resolve eq93 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq96 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (M.op X1 X0) X2) ∨ (M.op X1 X0) = X2 ∨ (M.op X0 X2) ≠ X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94 X0 X1 X2
       have i₂ := eq47 X1 X0 X2
       grind)
    | (have i₁ := eq94 X0 X1 X0
       have i₂ := eq47 X0 (M.op X1 X0) x
       grind)
    | exact superpose eq47 eq94
    | (have j0 := eq94 X0 X1 X2
       grind)
    | (have r₁ := eq94 x X1 (M.op X0 x)
       have r₂ := eq47 X0 x x
       grind)
    | exact resolve eq94 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq97 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X2 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 X0 X1 X2
       have i₂ := eq51 X1 X0 X2
       grind)
    | exact superpose eq51 eq95
    | (have j0 := eq95 X0 X1 X2
       grind)
    | exact resolve eq95 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq98 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ X2 ∨ (M.op X1 X0) = (k (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq96 X0 X1 X2
       have j1 := eq53 X0 X2 X2
       grind)
    | (have r₁ := eq96 X1 X0 X2
       have r₂ := eq53 X0 X1 (k (M.op X0 X1) X2)
       grind)
    | (have r₁ := eq96 X1 X0 X2
       have r₂ := eq53 X0 X1 X2
       grind)
    | (have r₁ := eq96 X0 X1 (M.op X0 X1)
       have r₂ := eq53 X0 X1 (M.op X1 X0)
       grind)
    | exact resolve eq96 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq96
  have eq152 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X3 X2) = (k (M.op X3 X2) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq98 X2 X3 (M.op X0 X1)
       have i₂ := eq47 X0 X1 X2
       grind)
    | exact superpose eq47 eq98
    | (have j0 := eq98 X2 X3 (M.op X0 X1)
       grind)
    | (have r₁ := eq98 x X1 (M.op X0 x)
       have r₂ := eq47 X0 x x
       grind)
    | exact resolve eq98 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq154 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (k (M.op X3 X2) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq152 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq161 : ∀ X0 X1 X2 X3 : G, (σ (M.op X1 X2)) = (k (σ (M.op X1 X2)) (σ (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15 (M.op X1 X2) (M.op X0 X3)
       have i₂ := eq154 X0 X3 X2 X1
       grind)
    | exact superpose eq154 eq15
    | exact resolve eq15 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq195 : ∀ X0 X1 X2 : G, (M.op X2 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 X1 X0 x
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq47
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq219 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq221 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq195 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq234 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq220 (σ (M.op X0 X1))
       have i₂ := eq161 X0 X0 X1 X1
       grind)
    | exact superpose eq161 eq220
    | (have j0 := eq220 (σ (M.op X0 X1))
       grind)
    | exact resolve eq220 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq239 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq234 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq244 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq221 X0 X1
       grind)
    | exact superpose eq221 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq221 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq221 X0 X1
       grind)
    | exact resolve eq13 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq244 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq517 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq239 X0 X1
       grind)
    | exact superpose eq239 eq47
    | exact resolve eq47 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq555 : ∀ X0 X1 X2 : G, (σ X1) = (M.op X2 (σ X1)) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq517 X0 X1 X2
       have i₂ := eq221 X0 X1
       grind)
    | exact superpose eq221 eq517
    | (have j1 := eq221 X2 (σ X1)
       grind)
    | exact resolve eq517 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq843 : ∀ X0 X1 : G, (k X0 (τ (σ X0))) = X0 ∨ (k X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0
       have i₂ := eq555 X1 X0 (σ X0)
       grind)
    | exact superpose eq555 eq72
    | (have j1 := eq555 X1 X0 x
       grind)
    | exact resolve eq72 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq848 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq843 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq843
    | (have j0 := eq843 X0 X1
       grind)
    | exact resolve eq843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq870 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq848 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq875 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq870 X0
       have j1 := eq220 X0
       grind)
    | (have r₁ := eq870 X0
       have r₂ := eq220 X0
       grind)
    | exact resolve eq870 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq870
  have eq881 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 X0
       have i₂ := eq875 X0
       grind)
    | exact superpose eq875 eq23
    | exact resolve eq23 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq882 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq875 X0
       grind)
    | exact superpose eq875 eq15
    | exact resolve eq15 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq882 X0
       have i₂ := eq875 (σ X0)
       grind)
    | exact superpose eq875 eq882
    | exact resolve eq882 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq884 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq881 X0
       have i₂ := eq875 (τ X0)
       grind)
    | exact superpose eq875 eq881
    | exact resolve eq881 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875 eq881
  have eq1457 : ∀ X0 X1 X2 : G, (k (σ X0) (σ (M.op X1 X2))) = (σ (M.op X2 X0)) ∨ (M.op X1 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 (M.op X1 X2)
       have i₂ := eq97 X1 X2 X0
       grind)
    | exact superpose eq97 eq15
    | (have j1 := eq97 X1 X2 X0
       grind)
    | exact resolve eq15 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2260 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq270 X0 X1
       grind)
    | exact superpose eq270 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq270 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq270 X0 X1
       grind)
    | exact resolve eq12 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2263 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X0 X1 X2
       have i₂ := eq270 X0 X1
       grind)
    | exact superpose eq270 eq51
    | (have j1 := eq270 X0 X1
       grind)
    | exact resolve eq51 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq2339 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2260 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq2932 : ∀ X0 X1 X2 X3 : G, (σ (M.op X1 X3)) = (k (σ X3) (k (σ X1) (σ (M.op X2 X0)))) ∨ (M.op X0 X1) = (M.op X1 X3) ∨ (M.op X0 X1) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1457 X3 X0 X1
       have i₂ := eq1457 X1 X2 X0
       grind)
    | exact superpose eq1457 eq1457
    | (have j0 := eq1457 X3 X0 X1
       have j1 := eq1457 X3 X0 X1
       grind)
    | exact resolve eq1457 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2950 : ∀ X0 X1 X2 X3 : G, (k (σ X1) (σ (M.op X2 X0))) = (k (σ X1) (σ (M.op X3 X0))) ∨ (M.op X0 X1) = (M.op X3 X0) ∨ (M.op X0 X1) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1457 X1 X2 X0
       have i₂ := eq1457 X1 X3 X0
       grind)
    | exact superpose eq1457 eq1457
    | (have j0 := eq1457 X1 X3 X0
       have j1 := eq1457 X1 X3 X0
       grind)
    | exact resolve eq1457 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2959 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (k (σ y) (σ (M.op X0 x))) ∨ (M.op x y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1457 y X0 x
       grind)
    | exact superpose eq1457 eq16
    | (have j1 := eq1457 y X0 x
       grind)
    | exact resolve eq16 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457
  have eq4573 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X2) (M.op X1 X2)) ∨ (M.op X1 X2) = (M.op X2 X0) ∨ (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X0) ∨ (k X0 (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq97 X1 X2 X0
       have i₂ := eq2339 X0 (M.op X1 X2)
       grind)
    | exact superpose eq2339 eq97
    | (have j0 := eq97 X1 X2 X0
       have j1 := eq2339 X0 (M.op X1 X2)
       grind)
    | exact resolve eq97 eq2339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339
  have eq4636 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X2) (M.op X1 X2)) ∨ (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X0) ∨ (k X0 (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq4573 X0 X1 X2
       have j1 := eq57 X2 X1 X0
       grind)
    | (have r₁ := eq4573 (M.op X1 X1) X1 X1
       have r₂ := eq57 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | (have r₁ := eq4573 X2 X1 X0
       have r₂ := eq57 X0 X1 X2
       grind)
    | (have r₁ := eq4573 X0 X0 X1
       have r₂ := eq57 X0 X1 X1
       grind)
    | exact resolve eq4573 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4573
  have eq4641 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 X0) ∨ (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X0) ∨ (k X0 (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4636 X0 X1 X2
       have i₂ := eq47 X1 X2 (M.op X1 X2)
       grind)
    | (have i₁ := eq4636 X0 X1 X2
       have i₂ := eq47 (M.op X1 X2) (M.op X1 X2) x
       grind)
    | exact superpose eq47 eq4636
    | (have j0 := eq4636 X0 X1 X2
       grind)
    | exact resolve eq4636 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4636
  have eq4642 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X0) ∨ (k X0 (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq4641 X0 X1 X2
       have j1 := eq57 X2 X1 X0
       grind)
    | (have r₁ := eq4641 X2 X1 X0
       have r₂ := eq57 X0 X1 X2
       grind)
    | (have r₁ := eq4641 X0 X0 X1
       have r₂ := eq57 X0 X1 X1
       grind)
    | exact resolve eq4641 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4641
  have eq4643 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X0 (M.op X1 X2)) ∨ (k X0 (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4642 X0 X1 X2
       have i₂ := eq51 X2 X1 X0
       grind)
    | exact superpose eq51 eq4642
    | (have j0 := eq4642 X0 X1 X2
       grind)
    | exact resolve eq4642 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4642
  have eq6144 : (M.op (σ x) (σ y)) ≠ (k (σ y) (M.op (σ x) (σ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2959 x
       have i₂ := eq883 x
       grind)
    | exact superpose eq883 eq2959
    | (have j0 := eq2959 x
       grind)
    | exact resolve eq2959 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2959
  have eq6792 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2263 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq20105 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (τ (k (σ X1) (k (σ X3) (σ (M.op X2 X0))))) ∨ (M.op X0 X3) = (M.op X3 X1) ∨ (M.op X2 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (M.op X3 X1)
       have i₂ := eq2932 X0 X3 X2 X1
       grind)
    | exact superpose eq2932 eq10
    | (have j1 := eq2932 X0 X3 X2 X1
       grind)
    | exact resolve eq10 eq2932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2932
  have eq20141 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (k X1 (τ (k (σ X3) (σ (M.op X2 X0))))) ∨ (M.op X0 X3) = (M.op X3 X1) ∨ (M.op X2 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20105 X0 X1 X2 X3
       have i₂ := eq20 (k (σ X3) (σ (M.op X2 X0))) X1
       grind)
    | exact superpose eq20 eq20105
    | (have j0 := eq20105 X0 X1 X2 X3
       grind)
    | exact resolve eq20105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq20105
  have eq20233 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (k X1 (k X3 (M.op X2 X0))) ∨ (M.op X0 X3) = (M.op X3 X1) ∨ (M.op X2 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20141 X0 X1 X2 X3
       have i₂ := eq17 X3 (M.op X2 X0)
       grind)
    | exact superpose eq17 eq20141
    | (have j0 := eq20141 X0 X1 X2 X3
       grind)
    | exact resolve eq20141 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20141
  have eq22013 : ∀ X0 X1 X2 X3 : G, (τ (k (σ X3) (σ (M.op X2 X0)))) = (k (τ (σ X3)) (τ (σ (M.op X1 X0)))) ∨ (M.op X1 X0) = (M.op X0 X3) ∨ (M.op X2 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 (σ (M.op X1 X0)) (σ X3)
       have i₂ := eq2950 X0 X3 X1 X2
       grind)
    | (have i₁ := eq23 (σ (M.op X1 X0)) (σ X3)
       have i₂ := eq2950 X0 X3 X2 X1
       grind)
    | exact superpose eq2950 eq23
    | (have j1 := eq2950 X0 X3 X1 X1
       grind)
    | exact resolve eq23 eq2950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2950
  have eq22085 : ∀ X0 X1 X2 X3 : G, (τ (k (σ X3) (σ (M.op X2 X0)))) = (k (τ (σ X3)) (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X3) ∨ (M.op X2 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22013 X0 X1 X2 X3
       have i₂ := eq10 (M.op X1 X0)
       grind)
    | exact superpose eq10 eq22013
    | (have j0 := eq22013 X0 X1 X1 X3
       grind)
    | exact resolve eq22013 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22013
  have eq22126 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op X1 X0)) = (τ (k (σ X3) (σ (M.op X2 X0)))) ∨ (M.op X1 X0) = (M.op X0 X3) ∨ (M.op X2 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22085 X0 X1 X2 X3
       have i₂ := eq10 X3
       grind)
    | exact superpose eq10 eq22085
    | (have j0 := eq22085 X0 X1 X1 X3
       grind)
    | exact resolve eq22085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22085
  have eq22138 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op X1 X0)) = (k X3 (M.op X2 X0)) ∨ (M.op X1 X0) = (M.op X0 X3) ∨ (M.op X2 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22126 X0 X1 X2 X3
       have i₂ := eq17 X3 (M.op X2 X0)
       grind)
    | exact superpose eq17 eq22126
    | (have j0 := eq22126 X0 X1 X1 X3
       grind)
    | exact resolve eq22126 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq22126
  have eq25160 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) ≠ (M.op (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X0 X2) = (k X2 (M.op X1 X0)) ∨ (M.op X2 X3) = (M.op (M.op X1 X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6792 X3 (M.op X1 X0) X2
       have i₂ := eq51 X0 X1 X3
       grind)
    | exact superpose eq51 eq6792
    | (have j0 := eq6792 (M.op X1 X0) X2 X3
       grind)
    | exact resolve eq6792 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6792
  have eq25199 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 (M.op X1 X0)) ∨ (M.op X2 X3) = (M.op (M.op X1 X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25160 X0 X1 X2 X3
       have i₂ := eq47 X1 X0 (M.op X1 X0)
       grind)
    | (have i₁ := eq25160 X0 X1 X2 X3
       have i₂ := eq47 (M.op X1 X0) (M.op X1 X0) x
       grind)
    | exact superpose eq47 eq25160
    | (have j0 := eq25160 X0 X1 X2 X3
       grind)
    | (have r₁ := eq25160 x x x X3
       have r₂ := eq47 x x (M.op x x)
       grind)
    | (have r₁ := eq25160 x X1 (M.op (M.op X1 x) (M.op X1 x)) X3
       have r₂ := eq47 (M.op X1 x) (M.op X1 x) x
       grind)
    | exact resolve eq25160 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25160
  have eq25200 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (k X2 (M.op X1 X0)) ∨ (M.op X2 X3) = (M.op (M.op X1 X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq25199 X0 X1 X2 X3
       have j1 := eq97 X1 X0 X2
       grind)
    | (have r₁ := eq25199 X1 X0 X2 X3
       have r₂ := eq97 X0 X1 X2
       grind)
    | (have r₁ := eq25199 X0 X1 X1 X3
       have r₂ := eq97 X0 X1 X0
       grind)
    | exact resolve eq25199 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq25199
  have eq25201 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (k X2 (M.op X1 X0)) ∨ (M.op X2 X3) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25200 X0 X1 X2 X3
       have i₂ := eq51 X0 X1 X3
       grind)
    | exact superpose eq51 eq25200
    | (have j0 := eq25200 X0 X1 X2 X3
       grind)
    | exact resolve eq25200 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25200
  have eq71927 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq6144
       have i₂ := eq4643 (σ y) (σ x) (σ x)
       grind)
    | exact superpose eq4643 eq6144
    | (have j1 := eq4643 (σ y) (σ x) (σ x)
       grind)
    | (have r₁ := eq6144
       have r₂ := eq4643 (σ y) (σ x) (σ x)
       grind)
    | exact resolve eq6144 eq4643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4643 eq6144
  have eq71955 : (σ y) = (k (σ y) (M.op (σ x) (σ x))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq71927
  have eq73253 : (τ (σ y)) = (k (τ (σ y)) (τ (M.op (σ x) (σ x)))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq23 (M.op (σ x) (σ x)) (σ y)
       have i₂ := eq71955
       grind)
    | exact superpose eq71955 eq23
    | exact resolve eq23 eq71955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq71955
  have eq73275 : (τ (σ y)) = (k (τ (σ y)) (M.op (τ (σ x)) (τ (σ x)))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq73253
       have i₂ := eq884 (σ x)
       grind)
    | exact superpose eq884 eq73253
    | exact resolve eq73253 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884 eq73253
  have eq73291 : (τ (σ y)) = (k (τ (σ y)) (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq73275
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq73275
    | exact resolve eq73275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73275
  have eq73299 : y = (k y (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq73291
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq73291
    | exact resolve eq73291 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73291
  have eq73302 : y = (k y (M.op x x)) := by
    first
    | (have j1 := eq57 x x y
       grind)
    | (have r₁ := eq73299
       have r₂ := eq57 x x y
       grind)
    | exact resolve eq73299 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73299
  have eq73316 : ∀ X0 : G, y = (M.op x y) ∨ (M.op x X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq73302
       have i₂ := eq25201 x x y X0
       grind)
    | exact superpose eq25201 eq73302
    | (have j1 := eq25201 y x x X0
       grind)
    | exact resolve eq73302 eq25201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25201
  have eq73337 : ∀ X0 : G, y = (k y (M.op X0 x)) ∨ (M.op x y) = (M.op X0 x) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq22138 x X0 x y
       have i₂ := eq73302
       grind)
    | exact superpose eq73302 eq22138
    | (have j0 := eq22138 x X0 X0 y
       grind)
    | exact resolve eq22138 eq73302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22138 eq73302
  have eq73367 : ∀ X0 : G, y = (k y (M.op X0 x)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq73337 X0
       have j1 := eq57 x X0 y
       grind)
    | (have r₁ := eq73337 y
       have r₂ := eq57 y x x
       grind)
    | (have r₁ := eq73337 x
       have r₂ := eq57 x x y
       grind)
    | (have r₁ := eq73337 X0
       have r₂ := eq57 x x y
       grind)
    | exact resolve eq73337 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq73337
  have eq74084 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (M.op y X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 x y x
       have i₂ := eq73316 X0
       grind)
    | exact superpose eq73316 eq47
    | (have j1 := eq73316 X1
       grind)
    | exact resolve eq47 eq73316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq74150 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op y X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq517 x y x
       have i₂ := eq73316 X0
       grind)
    | exact superpose eq73316 eq517
    | (have j1 := eq73316 X1
       grind)
    | exact resolve eq517 eq73316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq75691 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have j0 := eq74084 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74084
  have eq75709 : (M.op x y) = (M.op y y) := by
    first
    | (have j1 := eq73316 y
       grind)
    | (have r₁ := eq75691
       have r₂ := eq73316 x
       grind)
    | exact resolve eq75691 eq73316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73316 eq75691
  have eq75725 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq883 y
       have i₂ := eq75709
       grind)
    | exact superpose eq75709 eq883
    | exact resolve eq883 eq75709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76067 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75725
       grind)
    | exact superpose eq75725 eq16
    | exact resolve eq16 eq75725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76591 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op y y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq76067
       have i₂ := eq555 X0 y (σ y)
       grind)
    | exact superpose eq555 eq76067
    | (have j1 := eq555 X0 y x
       grind)
    | exact resolve eq76067 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76603 : ∀ X0 : G, (M.op y y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq76591 X0
       have j1 := eq555 X0 y x
       grind)
    | (have r₁ := eq76591 X0
       have r₂ := eq555 X0 y (σ x)
       grind)
    | exact resolve eq76591 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq76591
  have eq76604 : ∀ X0 : G, (M.op x y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq76603 X0
       have i₂ := eq75709
       grind)
    | exact superpose eq75709 eq76603
    | exact resolve eq76603 eq75709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75709 eq76603
  have eq77711 : ∀ X0 X1 : G, (k X1 y) = (M.op y X1) ∨ (M.op x y) = (M.op y X1) ∨ (M.op x y) = (M.op X0 x) ∨ (M.op x y) = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq20233 x X1 X0 y
       have i₂ := eq73367 X0
       grind)
    | exact superpose eq73367 eq20233
    | (have j0 := eq20233 x X1 X0 y
       grind)
    | exact resolve eq20233 eq73367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20233 eq73367
  have eq77734 : ∀ X1 : G, (k X1 y) = (M.op y X1) ∨ (M.op x y) = (M.op y X1) ∨ (M.op x y) = (M.op x x) := by
    intro X1
    first
    | (have j0 := eq77711 x X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77711
  have eq77742 : ∀ X1 : G, (M.op x y) = (M.op y X1) ∨ (M.op x y) = (M.op y X1) ∨ (M.op x y) = (M.op x x) := by
    intro X1
    first
    | (have i₁ := eq77734 X1
       have i₂ := eq76604 X1
       grind)
    | exact superpose eq76604 eq77734
    | (have j0 := eq77734 X1
       grind)
    | exact resolve eq77734 eq76604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76604 eq77734
  have eq77743 : ∀ X1 : G, (M.op x y) = (M.op y X1) ∨ (M.op x y) = (M.op x x) := by
    intro X1
    first
    | (have j0 := eq77742 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77742
  have eq80247 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op x X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq76067
       have i₂ := eq74150 (σ y) X0
       grind)
    | exact superpose eq74150 eq76067
    | (have j1 := eq74150 X0 X0
       grind)
    | exact resolve eq76067 eq74150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80279 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq80247 X0
       have j1 := eq74150 X0 X0
       grind)
    | (have r₁ := eq80247 X0
       have r₂ := eq74150 (σ x) x
       grind)
    | exact resolve eq80247 eq74150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74150 eq80247
  have eq81937 : ∀ X1 : G, (M.op x y) = (M.op x X1) ∨ (M.op x y) = (M.op x x) := by
    intro X1
    first
    | (have i₁ := eq77743 X1
       have i₂ := eq80279 X1
       grind)
    | exact superpose eq80279 eq77743
    | exact resolve eq77743 eq80279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77743 eq80279
  have eq81938 : (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq81937 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81937
  have eq81952 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq75725
       have i₂ := eq81938
       grind)
    | exact superpose eq81938 eq75725
    | exact resolve eq75725 eq81938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75725 eq81938
  have eq82134 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq81952
       have i₂ := eq883 x
       grind)
    | exact superpose eq883 eq81952
    | exact resolve eq81952 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883 eq81952
  have eq83093 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq51 (σ y) (σ y) X0
       have i₂ := eq82134
       grind)
    | exact superpose eq82134 eq51
    | exact resolve eq51 eq82134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82134
  have eq83260 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq83093 X0
       have i₂ := eq51 (σ x) (σ x) X0
       grind)
    | exact superpose eq51 eq83093
    | exact resolve eq83093 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq83093
  have eq83324 : False := by grind
  exact eq83324

/-- `Equation4410`: `x ◇ (x ◇ y) = (y ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4410 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4410 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4410.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X2) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq44 : ∀ X0 X1 : G, (σ (k (k x X0) X1)) = (k (k (σ x) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k x X0) X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq10
    | exact resolve eq10 eq36
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
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
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
  have eq86 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
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
  have eq93 : ∀ X0 : G, (k x (k y X0)) = (τ (k (σ x) (k (σ y) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq45 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq45
    | exact resolve eq45 eq37
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
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
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
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (k y (k y X0)) = (τ (k (σ y) (k (σ y) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq48 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq48
    | exact resolve eq48 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq48
    | (have j0 := eq48 (M.op x y)
       grind)
    | exact resolve eq48 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq125 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq143 : ∀ X0 : G, (k (k x X0) x) = (τ (k (k (σ x) (σ X0)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq60
    | exact resolve eq60 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq164 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq86 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq86
    | exact resolve eq86 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : (σ x) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq36 (M.op x x)
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq36
    | exact resolve eq36 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq181 : (σ x) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq176
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq176
    | exact resolve eq176 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq189 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq189
    | exact resolve eq189 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq207 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq218 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq207
    | exact resolve eq207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq336 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq336
    | exact resolve eq336 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 X2 : G, (k (τ X2) (k (τ X0) X1)) = (τ (k X2 (k X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq336 X2 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq336
    | exact resolve eq336 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 : G, (τ (k (k (σ x) (σ y)) X0)) = (k (k x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq99 eq427
    | exact resolve eq427 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq690 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 x X0 X3
       have i₂ := eq16 x X0 X1
       grind)
    | (have i₁ := eq16 (M.op X1 X1) X1 x
       have i₂ := eq16 X0 X1 (M.op (M.op X1 X1) X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X1 x
       grind)
    | (have i₁ := eq16 X0 X1 (M.op (M.op X1 X1) X1)
       have i₂ := eq16 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op X1 X1)
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X1 X1) ∨ (k X2 (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X2 (M.op X1 X1)
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq28
    | (have j0 := eq28 X2 (M.op X1 X1)
       grind)
    | exact resolve eq28 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X2 (M.op X0 X0)
       have i₂ := eq690 X0 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq28 X2 (M.op X0 X0)
       have i₂ := eq690 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq690 eq28
    | (have j0 := eq28 X2 (M.op X0 X0)
       grind)
    | exact resolve eq28 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X1))) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq693 X2 (M.op X3 X1) X3
       have i₂ := eq693 X3 X1 X0
       grind)
    | (have i₁ := eq693 X2 (M.op X3 X1) X3
       have i₂ := eq693 X0 X1 X3
       grind)
    | exact superpose eq693 eq693
    | exact resolve eq693 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq693 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq693
    | (have j0 := eq693 X0 y x
       grind)
    | exact resolve eq693 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq693
    | (have j0 := eq693 X0 (σ y) (σ x)
       grind)
    | exact resolve eq693 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq760 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 (M.op (M.op X1 X1) X3)
       have i₂ := eq693 (M.op X1 X1) X3 X2
       grind)
    | (have i₁ := eq16 X0 X1 (M.op (M.op X1 X1) X3)
       have i₂ := eq693 X2 X3 (M.op X1 X1)
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq775 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op x y))) = (M.op (M.op (M.op X0 y) (M.op X0 y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 y) X1
       have i₂ := eq743 X0
       grind)
    | (have i₁ := eq16 x (M.op x y) x
       have i₂ := eq743 X0
       grind)
    | exact superpose eq743 eq16
    | exact resolve eq16 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq690 X0 (M.op (M.op X0 X0) y) X1
       have i₂ := eq743 (M.op X0 X0)
       grind)
    | exact superpose eq743 eq690
    | exact resolve eq690 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq778 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op (M.op X1 X1) y)
       have i₂ := eq743 (M.op X1 X1)
       grind)
    | exact superpose eq743 eq16
    | exact resolve eq16 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq779 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq775 X0 x
       have i₂ := eq777 (M.op X0 y) x
       grind)
    | exact superpose eq777 eq775
    | exact resolve eq775 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq796 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq744 eq16
    | exact resolve eq16 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq744 eq690
    | exact resolve eq690 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq799 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq744 eq16
    | exact resolve eq16 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq796 X0 x
       have i₂ := eq777 (M.op X0 sF3) x
       grind)
    | exact superpose eq777 eq796
    | exact resolve eq796 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq803 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X1) := by
    intro X1
    first
    | (have i₁ := eq777 (M.op x x) X1
       have i₂ := eq777 x (M.op x x)
       grind)
    | exact superpose eq777 eq777
    | exact resolve eq777 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq744 (M.op x x)
       have i₂ := eq777 x (M.op (M.op x x) sF3)
       grind)
    | exact superpose eq777 eq744
    | exact resolve eq744 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq839 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X1) := by
    intro X1
    first
    | exact superpose eq828 eq803
    | exact resolve eq803 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq854 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op x (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq778 X2 (M.op X2 X0)
       have i₂ := eq16 X2 X0 X1
       grind)
    | (have i₁ := eq778 (M.op X1 X1) X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq778
    | exact resolve eq778 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq884 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq828 eq854
    | exact resolve eq854 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq887 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq884 x x X2
       have i₂ := eq777 x x
       grind)
    | exact superpose eq777 eq884
    | exact resolve eq884 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq884
  have eq890 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X2
    first
    | exact superpose eq828 eq887
    | exact resolve eq887 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq910 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq940 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq941 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq940 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq952 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq910 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq979 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq952 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq952 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq952 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq952 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq1028 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq941 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq941
    | (have j0 := eq941 (σ X0)
       grind)
    | exact resolve eq941 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1044 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (k X0 (M.op x (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq779 eq28
    | (have j0 := eq28 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq28 X0 (M.op x (M.op x y))
       have r₂ := eq779 (M.op x (M.op x y))
       grind)
    | exact resolve eq28 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq1054 : ∀ X0 : G, (k X0 (M.op x (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq1044 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1059 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq828 eq1054
    | exact resolve eq1054 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq1069 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq1059 eq35
    | exact resolve eq35 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1083 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1069 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1069
    | exact resolve eq1069 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1127 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) ≠ (σ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1083 eq941
    | (have j0 := eq941 (σ (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | (have r₁ := eq941 (σ (M.op (σ x) (M.op (σ x) (σ y))))
       have r₂ := eq1083 (σ (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq941 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by grind
  clear eq1127
  have eq1352 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq839 eq11
    | (have j0 := eq11 X0 X0
       grind)
    | exact resolve eq11 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq1370 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1352 X0
       have j1 := eq13 (M.op (σ x) (M.op (σ x) (σ y))) X0
       grind)
    | (have r₁ := eq1352 x
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq1352 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq1352 x
       have r₂ := eq13 (M.op (σ x) (M.op (σ x) (σ y))) x
       grind)
    | exact resolve eq1352 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq1374 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | (have j0 := eq1370 X0
       have j1 := eq28 (M.op (σ x) (M.op (σ x) (σ y))) X0
       grind)
    | (have r₁ := eq1370 x
       have r₂ := eq28 X0 x
       grind)
    | exact resolve eq1370 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1421 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op x y))) := by
    first
    | exact superpose eq1374 eq42
    | exact resolve eq42 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3799 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq930
       grind)
    | exact superpose eq930 eq41
    | exact resolve eq41 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3800 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3799
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3799
    | exact resolve eq3799 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3799
  have eq3802 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq3800
    | exact resolve eq3800 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3800
  have eq13287 : ∀ X0 X1 : G, (σ (k (k x X1) (k y X0))) = (k (k (σ x) (σ X1)) (k (σ y) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X1 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq44
    | exact resolve eq44 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq44
  have eq23269 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq1140 eq798
    | exact resolve eq798 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23272 : ∀ X0 : G, (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq1140 eq16
    | exact resolve eq16 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23294 : ∀ X0 : G, (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq1140 eq23272
    | exact resolve eq23272 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140 eq23272
  have eq23310 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq23269 eq23294
    | exact resolve eq23294 eq23269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23269 eq23294
  have eq23353 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq23310 eq15
    | exact resolve eq15 eq23310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30672 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3802 eq936
    | exact resolve eq936 eq3802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30679 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq30672
       have r₂ := eq27
       grind)
    | exact resolve eq30672 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30672
  have eq30686 : y = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30679 eq218
    | exact resolve eq218 eq30679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30679
  have eq30752 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq30686
    | exact resolve eq30686 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30686
  have eq30767 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq30752
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq30752
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq30752
       have r₂ := eq13 x y
       grind)
    | exact resolve eq30752 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30752
  have eq30773 : x = (k x (τ (σ y))) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30767 eq200
    | exact resolve eq200 eq30767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq30767
  have eq30846 : x = (k x y) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq30773
    | exact resolve eq30773 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30773
  have eq30869 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq979 y x
       grind)
    | (have r₁ := eq30846
       have r₂ := eq979 y x
       grind)
    | exact resolve eq30846 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30846
  have eq30881 : x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq30869
       have r₂ := eq13 x y
       grind)
    | exact resolve eq30869 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30869
  have eq30886 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq930
       have i₂ := eq30881
       grind)
    | exact superpose eq30881 eq930
    | exact resolve eq930 eq30881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq30888 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq30881
       grind)
    | exact superpose eq30881 eq41
    | exact resolve eq41 eq30881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq30889 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq30888
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30888
    | exact resolve eq30888 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30888
  have eq31343 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30889 eq3802
    | exact resolve eq3802 eq30889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3802
  have eq31346 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq30889 eq936
    | exact resolve eq936 eq30889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq31361 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq30886
       grind)
    | exact superpose eq30886 eq28
    | (have j0 := eq28 X0 y
       grind)
    | (have r₁ := eq28 X0 y
       have r₂ := eq30886
       grind)
    | exact resolve eq28 eq30886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31382 : ∀ X0 : G, (M.op y y) = (M.op y X0) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16 y y x
       have i₂ := eq30886
       grind)
    | exact superpose eq30886 eq16
    | exact resolve eq16 eq30886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31392 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 y))) = (M.op X1 (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq738 y y X0 X1
       have i₂ := eq30886
       grind)
    | exact superpose eq30886 eq738
    | exact resolve eq738 eq30886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31398 : (M.op y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq799 y y
       have i₂ := eq30886
       grind)
    | exact superpose eq30886 eq799
    | exact resolve eq799 eq30886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31399 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq31361 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31361
  have eq31401 : y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30886 eq31398
    | exact resolve eq31398 eq30886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31398
  have eq31406 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X1
    first
    | (have i₁ := eq31392 x X1
       have i₂ := eq778 x (M.op X1 y)
       grind)
    | exact superpose eq778 eq31392
    | exact resolve eq31392 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31392
  have eq31409 : ∀ X0 : G, y = (M.op y X0) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq30886 eq31382
    | exact resolve eq31382 eq30886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31382
  have eq31431 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq828 eq31406
    | exact resolve eq31406 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31406
  have eq31445 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq30886 eq31431
    | exact resolve eq31431 eq30886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30886 eq31431
  have eq31450 : ∀ X1 : G, y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op X1 y) := by
    intro X1
    first
    | exact superpose eq31401 eq31445
    | exact resolve eq31445 eq31401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31445
  have eq31456 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq31343
       grind)
    | exact superpose eq31343 eq28
    | (have j0 := eq28 X0 y
       grind)
    | (have r₁ := eq28 X0 y
       have r₂ := eq31343
       grind)
    | exact resolve eq28 eq31343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31487 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 y))) = (M.op X1 (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq738 y y X0 X1
       have i₂ := eq31343
       grind)
    | exact superpose eq31343 eq738
    | exact resolve eq738 eq31343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31493 : (M.op y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq799 y y
       have i₂ := eq31343
       grind)
    | exact superpose eq31343 eq799
    | exact resolve eq799 eq31343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31494 : ∀ X0 : G, y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq31456 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31456
  have eq31496 : y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31343 eq31493
    | exact resolve eq31493 eq31343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31493
  have eq31501 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X1
    first
    | (have i₁ := eq31487 x X1
       have i₂ := eq778 x (M.op X1 y)
       grind)
    | exact superpose eq778 eq31487
    | exact resolve eq31487 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31487
  have eq31526 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq828 eq31501
    | exact resolve eq31501 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31501
  have eq31540 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X1
    first
    | exact superpose eq31343 eq31526
    | exact resolve eq31526 eq31343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31343 eq31526
  have eq31545 : ∀ X1 : G, y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op X1 y) := by
    intro X1
    first
    | exact superpose eq31496 eq31540
    | exact resolve eq31540 eq31496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31540
  have eq31547 : y = (k y (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31346 eq218
    | exact resolve eq218 eq31346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq31551 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq31346 eq28
    | (have j0 := eq28 X0 (σ y)
       grind)
    | (have r₁ := eq28 X0 (σ y)
       have r₂ := eq31346
       grind)
    | exact resolve eq28 eq31346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31582 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 (σ y)))) = (M.op X1 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq31346 eq738
    | exact resolve eq738 eq31346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31588 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31346 eq799
    | exact resolve eq799 eq31346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31589 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq31551 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31551
  have eq31591 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31346 eq31588
    | exact resolve eq31588 eq31346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31588
  have eq31596 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X1
    first
    | (have i₁ := eq31582 x X1
       have i₂ := eq778 x (M.op X1 sF3)
       grind)
    | exact superpose eq778 eq31582
    | exact resolve eq31582 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31582
  have eq31615 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq32 eq31547
    | exact resolve eq31547 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31547
  have eq31620 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X1
    first
    | exact superpose eq828 eq31596
    | exact resolve eq31596 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31596
  have eq31630 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X1
    first
    | exact superpose eq31346 eq31620
    | exact resolve eq31620 eq31346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31346 eq31620
  have eq31633 : ∀ X1 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | exact superpose eq31591 eq31630
    | exact resolve eq31630 eq31591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31630
  have eq31701 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq799 x x
       have i₂ := eq31399 X0
       grind)
    | exact superpose eq31399 eq799
    | (have j1 := eq31399 X0
       grind)
    | exact resolve eq799 eq31399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31399
  have eq31704 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq31701 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31701
    | (have j0 := eq31701 X0
       grind)
    | exact resolve eq31701 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31701
  have eq31854 : y = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31401 eq23310
    | exact resolve eq23310 eq31401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31887 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq31854
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31854
    | exact resolve eq31854 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31854
  have eq32036 : y = (k x x) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq31887
       grind)
    | exact superpose eq31887 eq11
    | exact resolve eq11 eq31887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32053 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq799 x x
       have i₂ := eq31887
       grind)
    | exact superpose eq31887 eq799
    | exact resolve eq799 eq31887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32054 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) := by grind
  clear eq32036
  have eq32056 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq32053
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32053
    | exact resolve eq32053 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32053
  have eq32209 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq32056 eq23310
    | exact resolve eq23310 eq32056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32245 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq32209
    | exact resolve eq32209 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32209
  have eq34330 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq799 x x
       have i₂ := eq31450 X0
       grind)
    | exact superpose eq31450 eq799
    | (have j1 := eq31450 X0
       grind)
    | exact resolve eq799 eq31450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31450
  have eq34333 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq34330 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34330
    | (have j0 := eq34330 X0
       grind)
    | exact resolve eq34330 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34330
  have eq34371 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq32056 eq34333
    | exact resolve eq34333 eq32056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32056 eq34333
  have eq34486 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq799 x x
       have i₂ := eq31494 X0
       grind)
    | exact superpose eq31494 eq799
    | (have j1 := eq31494 X0
       grind)
    | exact resolve eq799 eq31494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31494
  have eq34489 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq34486 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34486
    | (have j0 := eq34486 X0
       grind)
    | exact resolve eq34486 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34486
  have eq34640 : y = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31496 eq23310
    | exact resolve eq23310 eq31496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31496
  have eq34674 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq34640
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34640
    | exact resolve eq34640 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34640
  have eq34830 : y = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq695 x x
       have i₂ := eq34674
       grind)
    | exact superpose eq34674 eq695
    | exact resolve eq695 eq34674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34840 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq799 x x
       have i₂ := eq34674
       grind)
    | exact superpose eq34674 eq799
    | exact resolve eq799 eq34674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34674
  have eq34843 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq34840
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34840
    | exact resolve eq34840 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34840
  have eq34853 : y = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq34830
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34830
    | exact resolve eq34830 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34830
  have eq34997 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq34843 eq23310
    | exact resolve eq23310 eq34843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35034 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq34997
    | exact resolve eq34997 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34997
  have eq38963 : ∀ X0 : G, y = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq695 x x
       have i₂ := eq31545 x
       grind)
    | exact superpose eq31545 eq695
    | (have j1 := eq31545 X0
       grind)
    | exact resolve eq695 eq31545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq38974 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq799 x x
       have i₂ := eq31545 X0
       grind)
    | exact superpose eq31545 eq799
    | (have j1 := eq31545 X0
       grind)
    | exact resolve eq799 eq31545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31545
  have eq38977 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq38974 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq38974
    | (have j0 := eq38974 X0
       grind)
    | exact resolve eq38974 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38974
  have eq38988 : ∀ X0 : G, y = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq38963 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq38963
    | (have j0 := eq38963 X0
       grind)
    | exact resolve eq38963 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38963
  have eq39016 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq34843 eq38977
    | exact resolve eq38977 eq34843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38977
  have eq39025 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq34853 eq38988
    | exact resolve eq38988 eq34853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34853 eq38988
  have eq39133 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq799 X0 x
       have i₂ := eq31589 (M.op X0 x)
       grind)
    | exact superpose eq31589 eq799
    | (have j1 := eq31589 X0
       grind)
    | exact resolve eq799 eq31589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39136 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq39133
    | (have j0 := eq39133 X0
       grind)
    | exact resolve eq39133 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39133
  have eq39290 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq31591 eq23310
    | exact resolve eq23310 eq31591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39291 : (σ y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31591 eq23353
    | exact resolve eq23353 eq31591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39312 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31591 eq778
    | exact resolve eq778 eq31591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39314 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq828 eq39312
    | exact resolve eq39312 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39312
  have eq39329 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq32 eq39291
    | exact resolve eq39291 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39291
  have eq39392 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq39314
    | exact resolve eq39314 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39314
  have eq39448 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31591 eq39392
    | exact resolve eq39392 eq31591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39392
  have eq39583 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq39329 eq28
    | (have j0 := eq28 X0 (σ x)
       grind)
    | exact resolve eq28 eq39329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39595 : ∀ X0 X1 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (k X1 (σ y)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq39329 eq719
    | exact resolve eq719 eq39329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39603 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq39329 eq11
    | exact resolve eq11 eq39329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39611 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq39329 eq696
    | exact resolve eq696 eq39329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39614 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 (σ x)))) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq39329 eq738
    | exact resolve eq738 eq39329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39621 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq39329 eq799
    | exact resolve eq799 eq39329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39329
  have eq39622 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq39603
  have eq39624 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq26 eq39621
    | exact resolve eq39621 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39621
  have eq39631 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (M.op X1 (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq26 eq39614
    | (have j0 := eq39614 X0 X1
       grind)
    | exact resolve eq39614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39614
  have eq39634 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq26 eq39611
    | (have j0 := eq39611 X0
       grind)
    | exact resolve eq39611 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39611
  have eq39664 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X1
    first
    | (have i₁ := eq39631 x X1
       have i₂ := eq778 x (M.op X1 sF2)
       grind)
    | exact superpose eq778 eq39631
    | exact resolve eq39631 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39631
  have eq39683 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq828 eq39664
    | exact resolve eq39664 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39664
  have eq39692 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X1
    first
    | exact superpose eq39624 eq39683
    | exact resolve eq39683 eq39624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39683
  have eq39717 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39448 eq11
    | exact resolve eq11 eq39448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39728 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 (σ x)))) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq39448 eq738
    | exact resolve eq738 eq39448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39735 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39448 eq799
    | exact resolve eq799 eq39448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39736 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq39717
  have eq39738 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq39735
    | exact resolve eq39735 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39735
  have eq39745 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (M.op X1 (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq39728
    | (have j0 := eq39728 X0 X1
       grind)
    | exact resolve eq39728 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39728
  have eq39778 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq39745 x X1
       have i₂ := eq778 x (M.op X1 sF2)
       grind)
    | exact superpose eq778 eq39745
    | exact resolve eq39745 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39745
  have eq39797 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq828 eq39778
    | exact resolve eq39778 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39778
  have eq39806 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq39738 eq39797
    | exact resolve eq39797 eq39738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39797
  have eq39899 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq39624 eq34843
    | exact resolve eq34843 eq39624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39624
  have eq39918 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq39899
  have eq41821 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39738 eq23310
    | exact resolve eq23310 eq39738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39738
  have eq44533 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq39290 eq799
    | exact resolve eq799 eq39290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39290
  have eq44536 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq26 eq44533
    | exact resolve eq44533 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44533
  have eq44692 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (σ y)) := by
    first
    | exact superpose eq44536 eq23310
    | exact resolve eq23310 eq44536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44536
  have eq47875 : ∀ X0 X1 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (k X1 (σ y)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    intro X0 X1
    first
    | exact superpose eq31615 eq719
    | exact resolve eq719 eq31615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq47891 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    intro X0
    first
    | exact superpose eq31615 eq696
    | exact resolve eq696 eq31615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq31615
  have eq47914 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    intro X0
    first
    | exact superpose eq26 eq47891
    | (have j0 := eq47891 X0
       grind)
    | exact resolve eq47891 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47891
  have eq47929 : ∀ X0 X1 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (k X1 (σ y)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq39595 eq47875
    | (have j0 := eq47875 X0 X1
       have j1 := eq39595 X0 X1
       grind)
    | exact resolve eq47875 eq39595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39595 eq47875
  have eq47951 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq39634 eq47914
    | (have j0 := eq47914 X0
       have j1 := eq39634 X0
       grind)
    | exact resolve eq47914 eq39634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39634 eq47914
  have eq47963 : ∀ X0 X1 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (k X1 (σ y)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq47929 X0 X1
       have j1 := eq979 (σ y) X1
       grind)
    | (have r₁ := eq47929 X0 (σ y)
       have r₂ := eq979 (σ y) X1
       grind)
    | (have r₁ := eq47929 X0 X1
       have r₂ := eq979 (σ y) X1
       grind)
    | exact resolve eq47929 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47929
  have eq47975 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq47951 X0
       have j1 := eq979 (σ y) X0
       grind)
    | (have r₁ := eq47951 (σ y)
       have r₂ := eq979 (σ y) x
       grind)
    | (have r₁ := eq47951 X0
       have r₂ := eq979 (σ y) x
       grind)
    | exact resolve eq47951 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47951
  have eq48031 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq31633 eq799
    | (have j1 := eq31633 X0
       grind)
    | exact resolve eq799 eq31633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31633
  have eq48034 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq48031
    | (have j0 := eq48031 X0
       grind)
    | exact resolve eq48031 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48031
  have eq48379 : ∀ X0 X1 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1083 X0
       have i₂ := eq31704 (M.op sF2 sF4)
       grind)
    | exact superpose eq31704 eq1083
    | (have j1 := eq31704 X1
       grind)
    | exact resolve eq1083 eq31704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48396 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1421
       have i₂ := eq31704 (M.op sF2 sF4)
       grind)
    | exact superpose eq31704 eq1421
    | (have j1 := eq31704 X0
       grind)
    | exact resolve eq1421 eq31704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421
  have eq48445 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq23310
       have i₂ := eq31704 (M.op sF2 sF4)
       grind)
    | exact superpose eq31704 eq23310
    | (have j1 := eq31704 X0
       grind)
    | exact resolve eq23310 eq31704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31704
  have eq48498 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq48445
    | (have j0 := eq48445 X0
       grind)
    | exact resolve eq48445 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48445
  have eq48525 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq48396
    | (have j0 := eq48396 X0
       grind)
    | exact resolve eq48396 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48396
  have eq48535 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ x = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq20 eq48379
    | (have j0 := eq48379 X0 X1
       grind)
    | exact resolve eq48379 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48379
  have eq48567 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq32245 eq48498
    | exact resolve eq48498 eq32245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48498
  have eq48589 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq48567 eq941
    | (have j0 := eq941 (σ y)
       grind)
    | (have r₁ := eq941 (σ y)
       have r₂ := eq48567 (σ y)
       grind)
    | exact resolve eq941 eq48567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48567
  have eq48668 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq48589
  have eq48851 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq48668 eq799
    | exact resolve eq799 eq48668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48856 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq48668 eq48851
    | exact resolve eq48851 eq48668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48668 eq48851
  have eq48997 : (σ y) = (σ (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq48856 eq23310
    | exact resolve eq23310 eq48856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49026 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq48856 eq778
    | exact resolve eq778 eq48856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49039 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq828 eq49026
    | exact resolve eq49026 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49026
  have eq49121 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26 eq49039
    | exact resolve eq49039 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49039
  have eq49182 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq48856 eq49121
    | exact resolve eq49121 eq48856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49121
  have eq49976 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq49182 eq27
    | exact resolve eq27 eq49182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49182
  have eq55818 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34371 eq26
    | (have j1 := eq34371 (σ x)
       grind)
    | exact resolve eq26 eq34371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34371
  have eq56194 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55818 eq31401
    | exact resolve eq31401 eq55818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31401
  have eq56203 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55818 eq39806
    | exact resolve eq39806 eq55818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55818
  have eq56223 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq56203
  have eq56227 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq56194
  have eq56251 : y = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31887 eq56227
    | exact resolve eq56227 eq31887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31887 eq56227
  have eq60993 : ∀ X0 X1 : G, (k X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1083 X0
       have i₂ := eq34489 (M.op sF2 sF4)
       grind)
    | exact superpose eq34489 eq1083
    | (have j1 := eq34489 X1
       grind)
    | exact resolve eq1083 eq34489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq61059 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq23310
       have i₂ := eq34489 (M.op sF2 sF4)
       grind)
    | exact superpose eq34489 eq23310
    | (have j1 := eq34489 X0
       grind)
    | exact resolve eq23310 eq34489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61070 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq39806 x
       have i₂ := eq34489 (M.op x sF4)
       grind)
    | exact superpose eq34489 eq39806
    | (have j1 := eq34489 X0
       grind)
    | exact resolve eq39806 eq34489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34489
  have eq61111 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq39918 eq61070
    | exact resolve eq61070 eq39918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61070
  have eq61118 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq61059
    | (have j0 := eq61059 X0
       grind)
    | exact resolve eq61059 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61059
  have eq61155 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq20 eq60993
    | (have j0 := eq60993 X0 X1
       grind)
    | exact resolve eq60993 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60993
  have eq61191 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq61111 X0
       have j1 := eq47975 X0
       grind)
    | (have r₁ := eq61111 X0
       have r₂ := eq47975 X0
       grind)
    | exact resolve eq61111 eq47975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61111
  have eq61193 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq35034 eq61118
    | exact resolve eq61118 eq35034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61118
  have eq61219 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq61193 eq941
    | (have j0 := eq941 (σ y)
       grind)
    | (have r₁ := eq941 (σ y)
       have r₂ := eq61193 (σ y)
       grind)
    | exact resolve eq941 eq61193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61193
  have eq61301 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq61219
  have eq61485 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq61301 eq799
    | exact resolve eq799 eq61301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61490 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq61301 eq61485
    | exact resolve eq61485 eq61301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61301 eq61485
  have eq61636 : (σ y) = (σ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq61490 eq23310
    | exact resolve eq23310 eq61490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61667 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq61490 eq778
    | exact resolve eq778 eq61490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61684 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq828 eq61667
    | exact resolve eq61667 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61667
  have eq61768 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26 eq61684
    | exact resolve eq61684 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61684
  have eq61829 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq61490 eq61768
    | exact resolve eq61768 eq61490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61768
  have eq61973 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq61829 eq27
    | exact resolve eq27 eq61829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68836 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39016 eq26
    | (have j1 := eq39016 (σ x)
       grind)
    | exact resolve eq26 eq39016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69137 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq68836 eq890
    | exact resolve eq890 eq68836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq69138 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq68836 eq1059
    | exact resolve eq1059 eq68836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69225 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq68836 eq39806
    | exact resolve eq39806 eq68836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68836
  have eq69247 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq69225
  have eq70590 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq69247 eq1374
    | exact resolve eq1374 eq69247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70669 : (σ y) = (σ (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq69247 eq44692
    | exact resolve eq44692 eq69247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44692
  have eq70676 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  have eq70681 : (σ y) = (σ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq70669
  have eq70688 : (σ y) = (σ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq70681
       have r₂ := eq70676
       grind)
    | exact resolve eq70681 eq70676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70676 eq70681
  have eq70753 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq26 eq70590
    | (have j0 := eq70590 X0
       grind)
    | exact resolve eq70590 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70590
  have eq70839 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq69247 eq70753
    | exact resolve eq70753 eq69247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69247 eq70753
  have eq72180 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq39025 eq798
    | exact resolve eq798 eq39025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq39025
  have eq72321 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq69138 eq72180
    | (have j1 := eq69138 y
       grind)
    | exact resolve eq72180 eq69138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72180
  have eq72393 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq26 eq72321
    | (have j0 := eq72321 X0
       grind)
    | exact resolve eq72321 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72321
  have eq72453 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq69138 eq72393
    | (have j1 := eq69138 y
       grind)
    | exact resolve eq72393 eq69138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69138 eq72393
  have eq73479 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq23310
       have i₂ := eq39136 (M.op sF2 sF4)
       grind)
    | exact superpose eq39136 eq23310
    | (have j1 := eq39136 X0
       grind)
    | exact resolve eq23310 eq39136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39136
  have eq73742 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq73479 eq941
    | (have j0 := eq941 (σ y)
       grind)
    | (have r₁ := eq941 (σ y)
       have r₂ := eq73479 (σ y)
       grind)
    | exact resolve eq941 eq73479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73479
  have eq73828 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by grind
  clear eq73742
  have eq74311 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 (σ y)))) = (M.op X1 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq73828 eq738
    | exact resolve eq738 eq73828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74333 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq74311 x X1
       have i₂ := eq778 x (M.op X1 sF3)
       grind)
    | exact superpose eq778 eq74311
    | exact resolve eq74311 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74311
  have eq74359 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    intro X1
    first
    | exact superpose eq828 eq74333
    | exact resolve eq74333 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74333
  have eq74376 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    intro X1
    first
    | exact superpose eq41821 eq74359
    | exact resolve eq74359 eq41821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74359
  have eq74384 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    intro X1
    first
    | exact superpose eq26 eq74376
    | (have j0 := eq74376 X1
       grind)
    | exact resolve eq74376 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74376
  have eq74388 : ∀ X1 : G, (σ y) = (M.op X1 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    intro X1
    first
    | exact superpose eq41821 eq74384
    | exact resolve eq74384 eq41821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74384
  have eq74392 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) := by
    intro X1
    first
    | exact superpose eq73828 eq74388
    | exact resolve eq74388 eq73828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73828 eq74388
  have eq78107 : ∀ X0 : G, (M.op x y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq69137 eq47963
    | (have j0 := eq47963 X0 X0
       grind)
    | exact resolve eq47963 eq69137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47963 eq69137
  have eq78179 : ∀ X0 : G, (M.op x y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq78107 X0
       have j1 := eq47975 X0
       grind)
    | (have r₁ := eq78107 X0
       have r₂ := eq47975 X0
       grind)
    | exact resolve eq78107 eq47975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47975 eq78107
  have eq78238 : ∀ X0 X1 : G, (σ y) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq48034 eq1059
    | (have j1 := eq48034 X1
       grind)
    | exact resolve eq1059 eq48034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059 eq48034
  have eq83476 : ∀ X0 : G, y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq941 y
       have i₂ := eq48535 X0 y
       grind)
    | exact superpose eq48535 eq941
    | (have j0 := eq941 y
       have j1 := eq48535 X0 x
       grind)
    | (have r₁ := eq941 y
       have r₂ := eq48535 X0 y
       grind)
    | (have r₁ := eq941 (σ (M.op x y))
       have r₂ := eq48535 (σ (M.op x y)) x
       grind)
    | exact resolve eq941 eq48535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48535
  have eq83545 : ∀ X0 : G, y = (M.op y y) ∨ x = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq83476 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83476
  have eq95197 : ∀ X0 : G, y ≠ y ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq941 y
       have i₂ := eq61155 X0 y
       grind)
    | exact superpose eq61155 eq941
    | (have j0 := eq941 y
       have j1 := eq61155 X0 x
       grind)
    | (have r₁ := eq941 y
       have r₂ := eq61155 X0 y
       grind)
    | (have r₁ := eq941 (σ (M.op x y))
       have r₂ := eq61155 (σ (M.op x y)) x
       grind)
    | exact resolve eq941 eq61155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61155
  have eq95265 : ∀ X0 : G, y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq95197 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95197
  have eq98298 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ y) (σ y)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq72453 eq11
    | (have j0 := eq11 X0 X0
       grind)
    | exact resolve eq11 eq72453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72453
  have eq98426 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq98298 X0
       have j1 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq98298 x
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq98298 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq98298 x
       have r₂ := eq13 (σ y) x
       grind)
    | exact resolve eq98298 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98298
  have eq98497 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq98426 X0
       have j1 := eq28 (σ y) X0
       grind)
    | (have r₁ := eq98426 x
       have r₂ := eq28 X0 x
       grind)
    | exact resolve eq98426 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98426
  have eq100247 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 y))) = (M.op X1 (M.op y y)) ∨ x = (M.op x y) ∨ (k X2 (σ (M.op x y))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq738 y y X0 X1
       have i₂ := eq83545 X2
       grind)
    | exact superpose eq83545 eq738
    | (have j1 := eq83545 X2
       grind)
    | exact resolve eq738 eq83545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100254 : ∀ X0 : G, (M.op y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq799 y y
       have i₂ := eq83545 X0
       grind)
    | exact superpose eq83545 eq799
    | (have j1 := eq83545 X0
       grind)
    | exact resolve eq799 eq83545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100269 : ∀ X0 : G, y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq83545 eq100254
    | (have j0 := eq100254 X0
       have j1 := eq83545 X0
       grind)
    | exact resolve eq100254 eq83545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100254
  have eq100275 : ∀ X1 X2 : G, (M.op x (M.op x y)) = (M.op X1 (M.op y y)) ∨ x = (M.op x y) ∨ (k X2 (σ (M.op x y))) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq100247 x X1 X2
       have i₂ := eq778 x (M.op X1 y)
       grind)
    | exact superpose eq778 eq100247
    | (have j0 := eq100247 x X1 X2
       grind)
    | exact resolve eq100247 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100247
  have eq100321 : ∀ X1 X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op y y)) ∨ x = (M.op x y) ∨ (k X2 (σ (M.op x y))) = X2 := by
    intro X1 X2
    first
    | exact superpose eq828 eq100275
    | (have j0 := eq100275 X1 X2
       grind)
    | exact resolve eq100275 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100275
  have eq100343 : ∀ X1 X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 y) ∨ x = (M.op x y) ∨ (k X2 (σ (M.op x y))) = X2 := by
    intro X1 X2
    first
    | exact superpose eq83545 eq100321
    | (have j0 := eq100321 X1 X2
       have j1 := eq83545 X2
       grind)
    | exact resolve eq100321 eq83545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83545 eq100321
  have eq100349 : ∀ X1 X2 : G, y = (M.op X1 y) ∨ x = (M.op x y) ∨ (k X2 (σ (M.op x y))) = X2 := by
    intro X1 X2
    first
    | exact superpose eq100269 eq100343
    | (have j0 := eq100343 X1 X2
       have j1 := eq100269 X2
       grind)
    | exact resolve eq100343 eq100269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100343
  have eq102530 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 y))) = (M.op X1 (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k X2 (σ (M.op x y))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq738 y y X0 X1
       have i₂ := eq95265 X2
       grind)
    | exact superpose eq95265 eq738
    | (have j1 := eq95265 X2
       grind)
    | exact resolve eq738 eq95265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102537 : ∀ X0 : G, (M.op y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq799 y y
       have i₂ := eq95265 X0
       grind)
    | exact superpose eq95265 eq799
    | (have j1 := eq95265 X0
       grind)
    | exact resolve eq799 eq95265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102552 : ∀ X0 : G, y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq95265 eq102537
    | (have j0 := eq102537 X0
       have j1 := eq95265 X0
       grind)
    | exact resolve eq102537 eq95265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102537
  have eq102558 : ∀ X1 X2 : G, (M.op x (M.op x y)) = (M.op X1 (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k X2 (σ (M.op x y))) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq102530 x X1 X2
       have i₂ := eq778 x (M.op X1 y)
       grind)
    | exact superpose eq778 eq102530
    | (have j0 := eq102530 x X1 X2
       grind)
    | exact resolve eq102530 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102530
  have eq102602 : ∀ X1 X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k X2 (σ (M.op x y))) = X2 := by
    intro X1 X2
    first
    | exact superpose eq828 eq102558
    | (have j0 := eq102558 X1 X2
       grind)
    | exact resolve eq102558 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102558
  have eq102626 : ∀ X1 X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 y) ∨ (σ (M.op x y)) = (σ x) ∨ (k X2 (σ (M.op x y))) = X2 := by
    intro X1 X2
    first
    | exact superpose eq95265 eq102602
    | (have j0 := eq102602 X1 X2
       have j1 := eq95265 X2
       grind)
    | exact resolve eq102602 eq95265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95265 eq102602
  have eq102631 : ∀ X1 X2 : G, y = (M.op X1 y) ∨ (σ (M.op x y)) = (σ x) ∨ (k X2 (σ (M.op x y))) = X2 := by
    intro X1 X2
    first
    | exact superpose eq102552 eq102626
    | (have j0 := eq102626 X1 X2
       have j1 := eq102552 X2
       grind)
    | exact resolve eq102626 eq102552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102626
  have eq103132 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq98497 eq164
    | exact resolve eq164 eq98497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq98497
  have eq103142 : y = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq32 eq103132
    | exact resolve eq103132 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103132
  have eq103143 : y = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq103142
  have eq103962 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ y = (τ y) := by
    intro X0
    first
    | (have i₁ := eq23353
       have i₂ := eq100269 (M.op sF2 sF4)
       grind)
    | exact superpose eq100269 eq23353
    | (have j1 := eq100269 X0
       grind)
    | exact resolve eq23353 eq100269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100269
  have eq104244 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (τ y) := by
    first
    | exact superpose eq103962 eq941
    | (have j0 := eq941 (σ (M.op x y))
       grind)
    | (have r₁ := eq941 (σ (M.op x y))
       have r₂ := eq103962 (σ (M.op x y))
       grind)
    | exact resolve eq941 eq103962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103962
  have eq104330 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (τ y) := by grind
  clear eq104244
  have eq104547 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (τ y) := by
    first
    | exact superpose eq104330 eq799
    | exact resolve eq799 eq104330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104555 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (τ y) := by
    first
    | exact superpose eq104330 eq104547
    | exact resolve eq104547 eq104330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104330 eq104547
  have eq104772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ x = (M.op x y) ∨ y = (τ y) := by
    first
    | exact superpose eq104555 eq39692
    | exact resolve eq39692 eq104555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104555
  have eq104832 : y = (τ y) ∨ y = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq104772
       have r₂ := eq27
       grind)
    | exact resolve eq104772 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104772
  have eq108163 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq100349 x X0
       grind)
    | exact superpose eq100349 eq18
    | (have j1 := eq100349 x X0
       grind)
    | exact resolve eq18 eq100349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100349
  have eq108500 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq108163 eq941
    | (have j0 := eq941 (σ (M.op x y))
       grind)
    | (have r₁ := eq941 (σ (M.op x y))
       have r₂ := eq108163 (σ (M.op x y))
       grind)
    | exact resolve eq941 eq108163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108572 : (τ (σ (M.op x y))) = (k (M.op x y) (τ (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq108163 eq125
    | exact resolve eq125 eq108163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq108163
  have eq108586 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq108500
  have eq108596 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq108572
    | exact resolve eq108572 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108572
  have eq108740 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 (σ (M.op x y))))) = (M.op X1 (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq108586 eq738
    | exact resolve eq738 eq108586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108747 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq108586 eq799
    | exact resolve eq799 eq108586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108755 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq108586 eq108747
    | exact resolve eq108747 eq108586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108747
  have eq108761 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq108740 x X1
       have i₂ := eq778 x (M.op X1 sF1)
       grind)
    | exact superpose eq778 eq108740
    | exact resolve eq108740 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108740
  have eq108794 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq828 eq108761
    | exact resolve eq108761 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108761
  have eq108812 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq108586 eq108794
    | exact resolve eq108794 eq108586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108586 eq108794
  have eq108817 : ∀ X1 : G, (σ (M.op x y)) = (M.op X1 (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq108755 eq108812
    | exact resolve eq108812 eq108755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108812
  have eq109185 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq108755 eq48856
    | exact resolve eq48856 eq108755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48856
  have eq109190 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq108755 eq61490
    | exact resolve eq61490 eq108755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq108755 eq39806
    | exact resolve eq39806 eq108755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109228 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq109185
  have eq109263 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq109201
       have r₂ := eq27
       grind)
    | exact resolve eq109201 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109201
  have eq109270 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq109190
       have r₂ := eq61973
       grind)
    | exact resolve eq109190 eq61973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109190
  have eq109273 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq109228
       have r₂ := eq49976
       grind)
    | exact resolve eq109228 eq49976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49976 eq109228
  have eq109384 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq32245 eq109270
    | exact resolve eq109270 eq32245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32245 eq109270
  have eq109429 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq109273 eq29
    | exact resolve eq29 eq109273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110675 : y = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq108817 y
       have i₂ := eq31409 sF1
       grind)
    | exact superpose eq31409 eq108817
    | exact resolve eq108817 eq31409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31409 eq108817
  have eq110933 : y = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq110675
  have eq111027 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq109273 eq110933
    | exact resolve eq110933 eq109273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110933
  have eq111028 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq111027
  have eq111676 : y = (k x x) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq111028
       grind)
    | exact superpose eq111028 eq11
    | exact resolve eq11 eq111028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111694 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq799 x x
       have i₂ := eq111028
       grind)
    | exact superpose eq111028 eq799
    | exact resolve eq799 eq111028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111028
  have eq111695 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq111676
  have eq111697 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq111694
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111694
    | exact resolve eq111694 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111694
  have eq114713 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq109263 eq108755
    | exact resolve eq108755 eq109263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108755 eq109263
  have eq114719 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq114713
  have eq114736 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq114719
    | exact resolve eq114719 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114719
  have eq114816 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq114736
       have r₂ := eq27
       grind)
    | exact resolve eq114736 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114736
  have eq114893 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114816 eq27
    | exact resolve eq27 eq114816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115000 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114816 eq111697
    | exact resolve eq111697 eq114816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111697
  have eq115001 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq115000
  have eq115086 : (M.op x y) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq109273 eq114893
    | exact resolve eq114893 eq109273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109273 eq114893
  have eq115193 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq115001 eq11
    | exact resolve eq11 eq115001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115001
  have eq115212 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq115193
  have eq115229 : (M.op x y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq115212
       have r₂ := eq115086
       grind)
    | exact resolve eq115212 eq115086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115086 eq115212
  have eq115319 : (k x x) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq115229 eq98
    | exact resolve eq98 eq115229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115229
  have eq115348 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq109429 eq115319
    | exact resolve eq115319 eq109429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109429 eq115319
  have eq115422 : (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq109384 eq29
    | exact resolve eq29 eq109384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109384
  have eq115606 : x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq30 eq115422
    | exact resolve eq115422 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115422
  have eq115607 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq115606
  have eq115755 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115607 eq48997
    | exact resolve eq48997 eq115607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48997
  have eq115779 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115607 eq61636
    | exact resolve eq61636 eq115607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61636 eq115607
  have eq115837 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq115779
  have eq115859 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq115755
  have eq115908 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq115837
    | exact resolve eq115837 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115837
  have eq115909 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq115908
  have eq115917 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq115859
    | exact resolve eq115859 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115859
  have eq115918 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq115917
  have eq115979 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115918 eq29
    | exact resolve eq29 eq115918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq116047 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq115918 eq48525
    | (have j0 := eq48525 X0
       grind)
    | exact resolve eq48525 eq115918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48525
  have eq116104 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq116047 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116047
  have eq116124 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq108596 eq116104
    | exact resolve eq116104 eq108596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108596 eq116104
  have eq116166 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq116124 X0
       have j1 := eq979 (M.op x y) X0
       grind)
    | (have r₁ := eq116124 X0
       have r₂ := eq979 (M.op x y) x
       grind)
    | (have r₁ := eq116124 (M.op x y)
       have r₂ := eq979 (M.op x y) x
       grind)
    | exact resolve eq116124 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq116124
  have eq116310 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116166 eq941
    | (have j0 := eq941 (M.op x y)
       grind)
    | (have r₁ := eq941 (M.op x y)
       have r₂ := eq116166 (M.op x y)
       grind)
    | exact resolve eq941 eq116166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116379 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq116310
  have eq116568 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 (M.op x y)))) = (M.op X1 (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq116379 eq738
    | exact resolve eq738 eq116379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116575 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116379 eq799
    | exact resolve eq799 eq116379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116582 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116379 eq116575
    | exact resolve eq116575 eq116379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116575
  have eq116588 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq116568 x X1
       have i₂ := eq778 x (M.op X1 sF0)
       grind)
    | exact superpose eq778 eq116568
    | exact resolve eq116568 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116568
  have eq116610 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq828 eq116588
    | exact resolve eq116588 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116588
  have eq116625 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op x y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq116379 eq116610
    | exact resolve eq116610 eq116379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116379 eq116610
  have eq116630 : ∀ X1 : G, (M.op x y) = (M.op X1 (M.op x y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq116582 eq116625
    | exact resolve eq116625 eq116582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116625
  have eq116638 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56223 eq116582
    | exact resolve eq116582 eq56223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56223
  have eq116695 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq116582 eq1374
    | exact resolve eq1374 eq116582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq116811 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq116638
  have eq116900 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq116811
    | exact resolve eq116811 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116811
  have eq116901 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq116900
  have eq127121 : ∀ X0 : G, (k (k (σ x) (σ y)) (k (σ y) (σ X0))) = (σ (k (k x (σ y)) (k y X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq70688 eq13287
    | exact resolve eq13287 eq70688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13287
  have eq127153 : ∀ X0 : G, (k (σ x) (k (σ y) (σ X0))) = (σ (k (k x (σ y)) (k y X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq30889 eq127121
    | exact resolve eq127121 eq30889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127121
  have eq127264 : ∀ X0 : G, (k (σ x) (k (σ y) (σ X0))) = (σ (k (k (M.op x y) (σ y)) (k y X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq116901 eq127153
    | exact resolve eq127153 eq116901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116901 eq127153
  have eq127361 : ∀ X0 : G, (k (σ x) (k (σ y) (σ X0))) = (σ (k (k (M.op x y) (σ y)) (k (σ y) X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq39918 eq127264
    | exact resolve eq127264 eq39918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39918 eq127264
  have eq127429 : ∀ X0 : G, (k (σ x) (k (σ y) (σ X0))) = (σ (k (M.op x y) (k (σ y) X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq61191 eq127361
    | exact resolve eq127361 eq61191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127361
  have eq127475 : ∀ X0 : G, (k (σ x) (k (σ y) (σ X0))) = (k (σ (M.op x y)) (σ (k (σ y) X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq38 eq127429
    | exact resolve eq127429 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq127429
  have eq127507 : ∀ X0 : G, (k (σ x) (k (σ y) (σ X0))) = (k (σ (M.op x y)) (σ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq70839 eq127475
    | exact resolve eq127475 eq70839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127475
  have eq127520 : ∀ X0 : G, (k (σ (M.op x y)) (σ y)) = (k (σ x) (k (σ y) (σ X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq70688 eq127507
    | exact resolve eq127507 eq70688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70688 eq127507
  have eq127526 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (k (σ y) (σ X0))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq61191 eq127520
    | exact resolve eq127520 eq61191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61191 eq127520
  have eq127529 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq70839 eq127526
    | exact resolve eq127526 eq70839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70839 eq127526
  have eq127531 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq30889 eq127529
    | exact resolve eq127529 eq30889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127529
  have eq127532 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq127531
  have eq127537 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq61829 eq127532
    | exact resolve eq127532 eq61829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127639 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq127532 eq61829
    | exact resolve eq61829 eq127532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127656 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq127639
  have eq127663 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq127537
  have eq127903 : (k x y) = (τ (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq127656 eq99
    | exact resolve eq99 eq127656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq127913 : (k y (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq127656 eq117
    | exact resolve eq117 eq127656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq127656
  have eq128249 : (k x (M.op x y)) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq100 eq127913
    | exact resolve eq127913 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq127913
  have eq128259 : (k x x) = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq98 eq127903
    | exact resolve eq127903 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127903
  have eq128322 : (k x (M.op x y)) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq61829 eq128249
    | exact resolve eq128249 eq61829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128249
  have eq128332 : x = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq128259
       have i₂ := eq30881
       grind)
    | exact superpose eq30881 eq128259
    | exact resolve eq128259 eq30881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128259
  have eq128382 : y = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq103143 eq128322
    | exact resolve eq128322 eq103143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103143 eq128322
  have eq128392 : x = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq61829 eq128332
    | exact resolve eq128332 eq61829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128332
  have eq128437 : y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq115909 eq128382
    | exact resolve eq128382 eq115909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128382
  have eq128447 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq115909 eq128392
    | exact resolve eq128392 eq115909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115909 eq128392
  have eq128488 : (σ y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq35034 eq128437
    | exact resolve eq128437 eq35034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35034 eq128437
  have eq128522 : (σ x) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq127663 eq128488
    | exact resolve eq128488 eq127663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128488
  have eq128551 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq128447 eq128522
    | exact resolve eq128522 eq128447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128447 eq128522
  have eq128801 : (M.op x y) ≠ (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq127663
  have eq128869 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq128801
       have r₂ := eq128551
       grind)
    | exact resolve eq128801 eq128551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128551 eq128801
  have eq129617 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (τ y) := by
    intro X0
    first
    | (have i₁ := eq23353
       have i₂ := eq102552 (M.op sF2 sF4)
       grind)
    | exact superpose eq102552 eq23353
    | (have j1 := eq102552 X0
       grind)
    | exact resolve eq23353 eq102552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23353 eq102552
  have eq129902 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (τ y) := by
    first
    | exact superpose eq129617 eq941
    | (have j0 := eq941 (σ (M.op x y))
       grind)
    | (have r₁ := eq941 (σ (M.op x y))
       have r₂ := eq129617 (σ (M.op x y))
       grind)
    | exact resolve eq941 eq129617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129617
  have eq129991 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (τ y) := by grind
  clear eq129902
  have eq130213 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (τ y) := by
    first
    | exact superpose eq129991 eq799
    | exact resolve eq799 eq129991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130220 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (τ y) := by
    first
    | exact superpose eq129991 eq130213
    | exact resolve eq130213 eq129991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129991 eq130213
  have eq130446 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (τ y) := by
    first
    | exact superpose eq130220 eq39692
    | exact resolve eq39692 eq130220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39692 eq130220
  have eq130507 : y = (τ y) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq130446
       have r₂ := eq27
       grind)
    | exact resolve eq130446 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130446
  have eq134016 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq102631 x X0
       grind)
    | exact superpose eq102631 eq18
    | (have j1 := eq102631 x X0
       grind)
    | exact resolve eq18 eq102631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102631
  have eq134380 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134016 eq941
    | (have j0 := eq941 (σ (M.op x y))
       grind)
    | (have r₁ := eq941 (σ (M.op x y))
       have r₂ := eq134016 (σ (M.op x y))
       grind)
    | exact resolve eq941 eq134016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134016
  have eq134470 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq134380
  have eq134624 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq134470 eq16
    | exact resolve eq16 eq134470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134641 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134470 eq799
    | exact resolve eq799 eq134470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134649 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134470 eq134641
    | exact resolve eq134641 eq134470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134641
  have eq134658 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq134470 eq134624
    | exact resolve eq134624 eq134470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134470 eq134624
  have eq135108 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134649 eq61490
    | exact resolve eq61490 eq134649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134649 eq39806
    | exact resolve eq39806 eq134649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134649
  have eq135151 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq135108
  have eq135192 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq135123
       have r₂ := eq27
       grind)
    | exact resolve eq135123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135123
  have eq135200 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq135151
       have r₂ := eq61973
       grind)
    | exact resolve eq135151 eq61973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61973 eq135151
  have eq135302 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127532 eq135192
    | exact resolve eq135192 eq127532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135192
  have eq136154 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq39016 eq134658
    | exact resolve eq134658 eq39016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136272 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134658 eq39016
    | exact resolve eq39016 eq134658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39016 eq134658
  have eq136295 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq136272
  have eq136314 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq136154
  have eq136334 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq34843 eq136295
    | exact resolve eq136295 eq34843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34843 eq136295
  have eq136394 : (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq135200 eq136314
    | exact resolve eq136314 eq135200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135200 eq136314
  have eq136419 : (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq128869 eq136334
    | exact resolve eq136334 eq128869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136334
  have eq136420 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ y) := by grind
  clear eq136419
  have eq136459 : (M.op x y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq135302 eq136394
    | exact resolve eq136394 eq135302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135302 eq136394
  have eq153096 : y = (σ y) ∨ y = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq104832
       grind)
    | exact superpose eq104832 eq14
    | exact resolve eq14 eq104832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104832
  have eq153176 : y = (σ y) ∨ y = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq153096
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq153096
    | exact resolve eq153096 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153096
  have eq153177 : y = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq153176
  have eq153206 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq114816 eq153177
    | exact resolve eq153177 eq114816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114816 eq153177
  have eq153268 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq153206 eq27
    | exact resolve eq27 eq153206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153380 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq153206 eq116582
    | exact resolve eq116582 eq153206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116582
  have eq153386 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by grind
  clear eq153380
  have eq153488 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq115918 eq153268
    | exact resolve eq153268 eq115918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153268
  have eq153767 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq153386 eq11
    | exact resolve eq11 eq153386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153386
  have eq153786 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by grind
  clear eq153767
  have eq153819 : (M.op x y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq153786
       have r₂ := eq153488
       grind)
    | exact resolve eq153786 eq153488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153786
  have eq153874 : (k x x) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq153819 eq98
    | exact resolve eq98 eq153819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153906 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq115979 eq153874
    | exact resolve eq153874 eq115979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153874
  have eq158091 : y = (σ y) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq130507
       grind)
    | exact superpose eq130507 eq14
    | exact resolve eq14 eq130507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130507
  have eq158172 : y = (σ y) ∨ y = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq158091
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq158091
    | exact resolve eq158091 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158091
  have eq158173 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by grind
  clear eq158172
  have eq158376 : (M.op x y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq158173 eq136420
    | exact resolve eq136420 eq158173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136420 eq158173
  have eq158379 : (M.op x y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ y) ∨ y = (σ y) := by grind
  clear eq158376
  have eq158398 : (M.op x y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq136459 eq158379
    | exact resolve eq158379 eq136459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136459 eq158379
  have eq158399 : (M.op x y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ y) := by grind
  clear eq158398
  have eq158613 : ∀ X0 : G, (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq158399 eq31589
    | (have j0 := eq31589 X0
       grind)
    | exact resolve eq31589 eq158399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31589
  have eq158619 : (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq158399 eq39448
    | exact resolve eq39448 eq158399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39448 eq158399
  have eq158664 : (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq158619
  have eq158670 : ∀ X0 : G, (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq158613 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158613
  have eq158710 : (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq127532 eq158664
    | exact resolve eq158664 eq127532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158664
  have eq158711 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq158710
  have eq158714 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq158670 X0
       have j1 := eq78179 X0
       grind)
    | (have r₁ := eq158670 X0
       have r₂ := eq78179 X0
       grind)
    | exact resolve eq158670 eq78179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78179 eq158670
  have eq158745 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq158711 eq158714
    | exact resolve eq158714 eq158711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158711 eq158714
  have eq159220 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq158745 eq941
    | (have j0 := eq941 (M.op x y)
       grind)
    | (have r₁ := eq941 (M.op x y)
       have r₂ := eq158745 (M.op x y)
       grind)
    | exact resolve eq941 eq158745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159226 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq158745 eq1028
    | (have j0 := eq1028 (M.op x y)
       grind)
    | exact resolve eq1028 eq158745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158745
  have eq159295 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq159226
  have eq159297 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq159220
  have eq159354 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq159295
    | exact resolve eq159295 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159295
  have eq159468 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq159297 eq799
    | exact resolve eq799 eq159297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159475 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq127532 eq159468
    | exact resolve eq159468 eq127532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159468
  have eq159501 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq159297 eq159475
    | exact resolve eq159475 eq159297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159297 eq159475
  have eq159873 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq159354 eq799
    | exact resolve eq799 eq159354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq159882 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq127532 eq159873
    | exact resolve eq159873 eq127532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127532 eq159873
  have eq159911 : (σ (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq159354 eq159882
    | exact resolve eq159882 eq159354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159354 eq159882
  have eq159933 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq159501 eq159911
    | exact resolve eq159911 eq159501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159501 eq159911
  have eq159983 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op (σ x) (σ x))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq159933 eq800
    | exact resolve eq800 eq159933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq160080 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq159933 eq61490
    | exact resolve eq61490 eq159933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160082 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq159933 eq61829
    | exact resolve eq61829 eq159933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61829 eq159933
  have eq160108 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq160082
  have eq160110 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq160080
  have eq160128 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq128869 eq160108
    | exact resolve eq160108 eq128869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160108
  have eq160129 : (M.op x y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq128869 eq160110
    | exact resolve eq160110 eq128869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160110
  have eq160194 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (σ x))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq828 eq159983
    | exact resolve eq159983 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159983
  have eq160198 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq160128 eq160129
    | exact resolve eq160129 eq160128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160129
  have eq160242 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ x) (σ x))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq61490 eq160194
    | exact resolve eq160194 eq61490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61490 eq160194
  have eq160274 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (σ x) (σ x))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq128869 eq160242
    | exact resolve eq160242 eq128869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128869 eq160242
  have eq160298 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq160128 eq160274
    | exact resolve eq160274 eq160128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160128 eq160274
  have eq160315 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq160198 eq160298
    | exact resolve eq160298 eq160198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160298
  have eq162444 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq160198 eq175
    | exact resolve eq175 eq160198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq160198
  have eq164501 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq162444 eq1028
    | (have j0 := eq1028 (M.op x y)
       grind)
    | exact resolve eq1028 eq162444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028 eq162444
  have eq164514 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq164501
  have eq164524 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq164514
    | exact resolve eq164514 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164514
  have eq165482 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq164524 eq16
    | exact resolve eq16 eq164524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165523 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq164524 eq165482
    | exact resolve eq165482 eq164524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164524 eq165482
  have eq166003 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq165523 eq160315
    | exact resolve eq160315 eq165523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160315 eq165523
  have eq166035 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq166003
  have eq166211 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq166035
  have eq192503 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq115348
       have i₂ := eq32054
       grind)
    | exact superpose eq32054 eq115348
    | exact resolve eq115348 eq32054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32054
  have eq192526 : y = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq192503
  have eq192559 : (σ y) = (σ (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq192526
       grind)
    | exact superpose eq192526 eq24
    | exact resolve eq24 eq192526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192594 : x = (k x (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30881
       have i₂ := eq192526
       grind)
    | exact superpose eq192526 eq30881
    | exact resolve eq30881 eq192526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192671 : (M.op x y) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by grind
  have eq192827 : (τ (k (k (σ x) (σ y)) (σ x))) = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq192559 eq143
    | exact resolve eq143 eq192559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq192559
  have eq193009 : (k (k x y) (τ (σ x))) = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq604 eq192827
    | exact resolve eq192827 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq192827
  have eq193115 : (k (k x y) x) = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq193009
    | exact resolve eq193009 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193009
  have eq193199 : (k x x) = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq193115
       have i₂ := eq30881
       grind)
    | exact superpose eq30881 eq193115
    | exact resolve eq193115 eq30881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30881 eq193115
  have eq193259 : y = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq111695 eq193199
    | exact resolve eq193199 eq111695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111695 eq193199
  have eq193284 : (σ y) = (k (k x (σ y)) x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq192526 eq193259
    | exact resolve eq193259 eq192526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192526 eq193259
  have eq193303 : (σ y) = (k x x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq192594 eq193284
    | exact resolve eq193284 eq192594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192594 eq193284
  have eq193317 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq115348 eq193303
    | exact resolve eq193303 eq115348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115348 eq193303
  have eq193327 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq193317
       have r₂ := eq192671
       grind)
    | exact resolve eq193317 eq192671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192671 eq193317
  have eq193333 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq193327
       grind)
    | exact superpose eq193327 eq24
    | exact resolve eq24 eq193327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193327
  have eq193504 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq193333
    | exact resolve eq193333 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193333
  have eq193526 : (M.op x y) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq115918 eq193504
    | exact resolve eq193504 eq115918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193504
  have eq193579 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq193526 eq26
    | exact resolve eq26 eq193526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193963 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq116630 eq193579
    | exact resolve eq193579 eq116630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116630 eq193579
  have eq194114 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq193963 eq27
    | exact resolve eq27 eq193963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193963
  have eq194427 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq194114
       have r₂ := eq115918
       grind)
    | exact resolve eq194114 eq115918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115918 eq194114
  have eq209027 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq39622 eq98
    | exact resolve eq98 eq39622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq209063 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq32 eq209027
    | exact resolve eq209027 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209027
  have eq210655 : ∀ X0 : G, x ≠ y ∨ (k X0 x) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq56251
       grind)
    | exact superpose eq56251 eq28
    | (have j0 := eq28 X0 x
       grind)
    | exact resolve eq28 eq56251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq56251
  have eq210732 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq210655 X0
       grind)
    | (have r₁ := eq210655 X0
       have r₂ := eq193526
       grind)
    | exact resolve eq210655 eq193526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193526 eq210655
  have eq210756 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq153206 eq210732
    | (have j0 := eq210732 X0
       grind)
    | exact resolve eq210732 eq153206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153206 eq210732
  have eq217695 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq153906
       have i₂ := eq210756 x
       grind)
    | exact superpose eq210756 eq153906
    | exact resolve eq153906 eq210756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153906 eq210756
  have eq217722 : (σ x) = (σ y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq217695
  have eq217845 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq217722 eq30889
    | exact resolve eq30889 eq217722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30889 eq217722
  have eq218131 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq153819 eq217845
    | exact resolve eq217845 eq153819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153819 eq217845
  have eq218212 : (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq218131
       have r₂ := eq153488
       grind)
    | exact resolve eq218131 eq153488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153488 eq218131
  have eq218241 : ∀ X0 : G, (k x (k y X0)) = (τ (k (σ x) (k (M.op x y) (σ X0)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq218212 eq93
    | exact resolve eq93 eq218212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq218246 : ∀ X0 : G, (k y (k y X0)) = (τ (k (M.op x y) (k (M.op x y) (σ X0)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq218212 eq110
    | exact resolve eq110 eq218212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq218212
  have eq218636 : ∀ X0 : G, (k y (k y X0)) = (k (τ (M.op x y)) (k (τ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq218246 x
       have i₂ := eq431 sF0 x sF0
       grind)
    | exact superpose eq431 eq218246
    | exact resolve eq218246 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq218246
  have eq218641 : ∀ X0 : G, (k x (k y X0)) = (k x (τ (k (M.op x y) (σ X0)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq91 eq218241
    | exact resolve eq218241 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq218241
  have eq218712 : ∀ X0 : G, (k y (k y X0)) = (k (M.op x y) (k (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq115979 eq218636
    | exact resolve eq218636 eq115979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218636
  have eq218717 : ∀ X0 : G, (k x (k y X0)) = (k x (k (τ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq218641 x
       have i₂ := eq336 sF0 x
       grind)
    | exact superpose eq336 eq218641
    | exact resolve eq218641 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336 eq218641
  have eq218782 : ∀ X0 : G, (M.op x y) = (k y (k y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq116695 eq218712
    | exact resolve eq218712 eq116695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218712
  have eq218787 : ∀ X0 : G, (k x (k y X0)) = (k x (k (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq115979 eq218717
    | exact resolve eq218717 eq115979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115979 eq218717
  have eq218838 : ∀ X0 : G, (M.op x y) = (k x (k x X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq194427 eq218782
    | exact resolve eq218782 eq194427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218782
  have eq218841 : ∀ X0 : G, (k x (M.op x y)) = (k x (k y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq116695 eq218787
    | exact resolve eq218787 eq116695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116695 eq218787
  have eq218881 : ∀ X0 : G, x = (k x (k y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq116166 eq218841
    | exact resolve eq218841 eq116166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116166 eq218841
  have eq218905 : ∀ X0 : G, x = (k x (k x X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq194427 eq218881
    | exact resolve eq218881 eq194427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194427 eq218881
  have eq218922 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq218838 eq218905
    | exact resolve eq218905 eq218838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218838 eq218905
  have eq218923 : x = (M.op x y) := by grind
  clear eq218922
  have eq218934 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq218923
       grind)
    | exact superpose eq218923 eq18
    | exact resolve eq18 eq218923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq218935 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq218923
       grind)
    | exact superpose eq218923 eq22
    | exact resolve eq22 eq218923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq218937 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq218923
       grind)
    | exact superpose eq218923 eq40
    | exact resolve eq40 eq218923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq218938 : (σ x) = (k (σ x) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq181
       have i₂ := eq218923
       grind)
    | exact superpose eq218923 eq181
    | exact resolve eq181 eq218923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq218958 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq828
       have i₂ := eq218923
       grind)
    | exact superpose eq218923 eq828
    | exact resolve eq828 eq218923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218990 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq209063
       have i₂ := eq218923
       grind)
    | exact superpose eq218923 eq209063
    | exact resolve eq209063 eq218923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209063
  have eq219017 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq218935 eq20
    | exact resolve eq20 eq218935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219885 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq218934 eq760
    | exact resolve eq760 eq218934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq222022 : (M.op (M.op x y) (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq218958 eq23310
    | exact resolve eq23310 eq218958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23310
  have eq222026 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq218958 eq31591
    | exact resolve eq31591 eq218958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31591
  have eq222073 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq218958 eq39806
    | exact resolve eq39806 eq218958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39806
  have eq223537 : (k (M.op x y) (M.op x y)) = (σ (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq222022
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq222022
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq222022 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222022
  have eq223707 : (k (M.op x y) (M.op x y)) = (σ (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq223537
  have eq223862 : (k (M.op x y) (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq42 eq223707
    | exact resolve eq223707 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq223707
  have eq224011 : (k (σ (M.op x y)) (σ x)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq219017 eq223862
    | exact resolve eq223862 eq219017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223862
  have eq224113 : (k (σ (M.op x y)) (σ x)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq224011
    | exact resolve eq224011 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224011
  have eq224184 : (k (σ x) (σ x)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq219017 eq224113
    | exact resolve eq224113 eq219017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224113
  have eq231063 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq222073 eq11
    | exact resolve eq11 eq222073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222073
  have eq231083 : (M.op (σ x) (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq231063
  have eq235948 : (σ y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq224184 eq39622
    | exact resolve eq39622 eq224184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224184
  have eq235987 : y = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq218990 eq235948
    | exact resolve eq235948 eq218990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218990 eq235948
  have eq235988 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq235987
  have eq243382 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq222026 eq219885
    | exact resolve eq219885 eq222026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222026
  have eq243389 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq243382
    | exact resolve eq243382 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243382
  have eq248842 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq243389
  have eq323626 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq231083 eq218937
    | exact resolve eq218937 eq231083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218937 eq231083
  have eq323744 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq323626
    | exact resolve eq323626 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323626
  have eq323763 : (k (σ x) (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq219017 eq323744
    | exact resolve eq323744 eq219017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323744
  have eq323777 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41821 eq323763
    | exact resolve eq323763 eq41821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41821 eq323763
  have eq324178 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq235988 eq218938
    | exact resolve eq218938 eq235988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218938 eq235988
  have eq324334 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq324178
    | exact resolve eq324178 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324178
  have eq324360 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq219017 eq324334
    | exact resolve eq324334 eq219017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324334
  have eq324380 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have j1 := eq39583 (σ x)
       grind)
    | (have r₁ := eq324360
       have r₂ := eq39583 x
       grind)
    | exact resolve eq324360 eq39583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39583 eq324360
  have eq324422 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq324380 eq39622
    | exact resolve eq39622 eq324380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39622
  have eq324468 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (σ y) := by grind
  clear eq324422
  have eq324512 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq324468 eq27
    | exact resolve eq27 eq324468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324468
  have eq324737 : (σ x) = (σ y) ∨ y = (σ y) := by
    first
    | (have r₁ := eq324512
       have r₂ := eq219017
       grind)
    | exact resolve eq324512 eq219017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324512
  have eq324810 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | exact superpose eq324737 eq26
    | exact resolve eq26 eq324737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324737
  have eq326268 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq324810 eq11
    | exact resolve eq11 eq324810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324810
  have eq326287 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq326268
  have eq326324 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq324380 eq326287
    | exact resolve eq326287 eq324380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324380 eq326287
  have eq326325 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq326324
  have eq326431 : (σ (M.op x y)) ≠ (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq326325 eq27
    | exact resolve eq27 eq326325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326325
  have eq326643 : y = (σ y) := by
    first
    | (have r₁ := eq326431
       have r₂ := eq219017
       grind)
    | exact resolve eq326431 eq219017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326431
  have eq326721 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq326643
       grind)
    | exact superpose eq326643 eq24
    | exact resolve eq24 eq326643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq326885 : (M.op x y) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq218934
       have i₂ := eq326643
       grind)
    | exact superpose eq326643 eq218934
    | exact resolve eq218934 eq326643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218934
  have eq326954 : (σ y) = (τ (σ y)) := by
    first
    | exact superpose eq326721 eq15
    | exact resolve eq15 eq326721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327898 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq326885 eq74392
    | exact resolve eq74392 eq326885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74392
  have eq327900 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq326885 eq78238
    | (have j0 := eq78238 X0 x
       grind)
    | exact resolve eq78238 eq326885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78238
  have eq345811 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq327900 eq941
    | (have j0 := eq941 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq941 (M.op (σ x) (σ y))
       have r₂ := eq327900 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq941 eq327900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq327900
  have eq345934 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq345811
  have eq346810 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 (M.op (σ x) (σ y))))) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq345934 eq738
    | exact resolve eq738 eq345934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq346818 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq345934 eq219885
    | exact resolve eq219885 eq345934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219885
  have eq346833 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq345934 eq346818
    | exact resolve eq346818 eq345934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346818
  have eq346840 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq346810 x X1
       have i₂ := eq778 x (M.op X1 sF4)
       grind)
    | exact superpose eq778 eq346810
    | exact resolve eq346810 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778 eq346810
  have eq346867 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X1
    first
    | exact superpose eq828 eq346840
    | exact resolve eq346840 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828 eq346840
  have eq346884 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X1
    first
    | exact superpose eq218958 eq346867
    | exact resolve eq346867 eq218958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218958 eq346867
  have eq346896 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X1
    first
    | exact superpose eq345934 eq346884
    | exact resolve eq346884 eq345934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345934 eq346884
  have eq346900 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X1
    first
    | exact superpose eq346833 eq346896
    | exact resolve eq346896 eq346833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346833 eq346896
  have eq369736 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq323777 eq39736
    | exact resolve eq39736 eq323777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39736 eq323777
  have eq369789 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq369736
  have eq370031 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq369789 eq248842
    | (have r₁ := eq248842
       have r₂ := eq369789
       grind)
    | exact resolve eq248842 eq369789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248842
  have eq370068 : (M.op x y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq369789
  have eq370100 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq370031
  have eq370101 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq370100
  have eq373709 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq370101 eq16
    | exact resolve eq16 eq370101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370101
  have eq373788 : ∀ X0 : G, (M.op x y) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq326885 eq373709
    | exact resolve eq373709 eq326885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373709
  have eq378127 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq373788 eq346900
    | exact resolve eq346900 eq373788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346900 eq373788
  have eq378130 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq378127
  have eq378212 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq378130
       have r₂ := eq370068
       grind)
    | exact resolve eq378130 eq370068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370068 eq378130
  have eq378377 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq378212 eq27
    | exact resolve eq27 eq378212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378212
  have eq378606 : (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq378377
       have r₂ := eq219017
       grind)
    | exact resolve eq378377 eq219017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378377
  have eq378680 : y = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq378606 eq32
    | exact resolve eq32 eq378606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq379008 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq378606 eq326954
    | exact resolve eq326954 eq378606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326954 eq378606
  have eq379094 : x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq379008
    | exact resolve eq379008 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379008
  have eq379201 : x = y ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq378680
    | exact resolve eq378680 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq378680
  have eq379209 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq379094
       have i₂ := eq218923
       grind)
    | exact superpose eq218923 eq379094
    | exact resolve eq379094 eq218923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379094
  have eq379287 : x = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq379201
       have i₂ := eq326643
       grind)
    | exact superpose eq326643 eq379201
    | exact resolve eq379201 eq326643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326643 eq379201
  have eq379363 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq379287
       have i₂ := eq218923
       grind)
    | exact superpose eq218923 eq379287
    | exact resolve eq379287 eq218923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218923 eq379287
  have eq379704 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq379209 eq327898
    | exact resolve eq327898 eq379209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327898 eq379209
  have eq379739 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ y) := by grind
  clear eq379704
  have eq379849 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq379739
    | exact resolve eq379739 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379739
  have eq379962 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq379849
       have r₂ := eq166211
       grind)
    | exact resolve eq379849 eq166211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166211 eq379849
  have eq380038 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq219017 eq379962
    | exact resolve eq379962 eq219017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379962
  have eq382407 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq379363 eq27
    | exact resolve eq27 eq379363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379363
  have eq382778 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq219017 eq382407
    | exact resolve eq382407 eq219017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219017 eq382407
  have eq382854 : (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq382778
       have r₂ := eq380038
       grind)
    | exact resolve eq382778 eq380038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380038 eq382778
  have eq383225 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq382854 eq326721
    | exact resolve eq326721 eq382854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326721 eq382854
  have eq383908 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq383225 eq218935
    | exact resolve eq218935 eq383225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218935
  have eq383909 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq383225 eq20
    | exact resolve eq20 eq383225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq383225
  have eq385010 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq383908 eq26
    | exact resolve eq26 eq383908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq383908
  have eq385581 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq326885 eq385010
    | exact resolve eq385010 eq326885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326885 eq385010
  have eq386275 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq385581 eq27
    | exact resolve eq27 eq385581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq385581
  have eq386597 : False := by grind
  exact eq386597

/-- `Equation4512`: `x ◇ (y ◇ z) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pyx_Equation4512 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4512 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4512.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X1) X2) := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op (M.op x y) X0) := by
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
  have eq176 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X1)
       have i₂ := eq174 (M.op X0 X1)
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (M.op (M.op x y) y) = (M.op x (k y y)) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq175
    | exact resolve eq175 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq320 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq320
    | exact resolve eq320 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq558 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq558 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq558
    | (have j0 := eq558 X0
       grind)
    | exact resolve eq558 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq562 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq559 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq559
    | (have j0 := eq559 X0
       grind)
    | exact resolve eq559 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq690 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (k X0 X1) X2) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
  have eq691 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (M.op X1 (M.op X2 X0)) ∨ (M.op X1 X2) = (M.op X0 X0) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 X0 (M.op X1 X2)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 (M.op X1 X2)
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = y := by
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
  have eq697 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq705 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq697
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq697
    | exact resolve eq697 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq709 : (M.op x y) = (k y x) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq693
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq693
    | exact resolve eq693 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq711 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (M.op X1 (M.op X2 X0)) ∨ (M.op X1 X2) = (k X0 X0) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq691 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq691
    | (have j0 := eq691 X0 X1 X2
       grind)
    | exact resolve eq691 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq712 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (k X0 X1) X2) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq690 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq690
    | (have j0 := eq690 X0 X1 X2
       grind)
    | exact resolve eq690 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq731 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq709
       grind)
    | exact superpose eq709 eq39
    | exact resolve eq39 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq732 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq731
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq731
    | exact resolve eq731 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq734 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq20 eq732
    | exact resolve eq732 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq737 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq734 eq705
    | exact resolve eq705 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq734
  have eq744 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | (have r₁ := eq737
       have r₂ := eq27
       grind)
    | exact resolve eq737 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq750 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq744 eq115
    | exact resolve eq115 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq744
  have eq759 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq29 eq750
    | exact resolve eq750 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq760 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq759
  have eq767 : (M.op (M.op x y) y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq183
       have i₂ := eq760
       grind)
    | exact superpose eq760 eq183
    | exact resolve eq183 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq769 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq760
       grind)
    | exact superpose eq760 eq40
    | exact resolve eq40 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq181 y X0
       have i₂ := eq760
       grind)
    | exact superpose eq760 eq181
    | exact resolve eq181 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq769
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq769
    | exact resolve eq769 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq776 : (k x x) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq767
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq767
    | exact resolve eq767 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq777 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq774
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq774
    | exact resolve eq774 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq795 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq777 eq181
    | exact resolve eq181 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq772 (M.op y X0)
       have i₂ := eq772 X0
       grind)
    | exact superpose eq772 eq772
    | exact resolve eq772 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833 : (M.op x y) = (M.op y (k y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq772 y
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq772
    | exact resolve eq772 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq839 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq832 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq844 : (M.op x y) = (M.op y (k y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq833
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq833
    | exact resolve eq833 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq845 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq839 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq839
    | exact resolve eq839 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq849 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq760 eq844
    | exact resolve eq844 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq851 : (M.op x x) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq772 x
       have i₂ := eq849
       grind)
    | exact superpose eq849 eq772
    | exact resolve eq772 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq852 : (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq849
       grind)
    | exact superpose eq849 eq175
    | exact resolve eq175 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq849
       grind)
    | exact superpose eq849 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq853
  have eq856 : (M.op x x) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq851
  have eq858 : (M.op x y) = (k x y) ∨ y = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq855
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq855
    | exact resolve eq855 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq859 : (k x x) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq856
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq856
    | exact resolve eq856 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq868 : (M.op x (M.op x y)) = (M.op y (k x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq859 eq772
    | exact resolve eq772 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq869 : (M.op (M.op x y) (M.op x y)) = (M.op x (k x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq859 eq175
    | exact resolve eq175 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq872 : (M.op x (M.op x y)) = (M.op y (k x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq868
  have eq875 : (k (M.op x y) (M.op x y)) = (M.op x (k x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq869
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq869
    | exact resolve eq869 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq876 : (M.op (M.op x y) x) = (M.op y (k x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq852 eq872
    | exact resolve eq872 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852 eq872
  have eq879 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq795 eq795
    | exact resolve eq795 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq880 : (M.op (σ x) (σ y)) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq795 sF3
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq795
    | exact resolve eq795 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (k X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op X0 X0) = (σ y) ∨ (σ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq795 X0
       have i₂ := eq11 X0 sF3
       grind)
    | exact superpose eq11 eq795
    | (have j1 := eq11 X0 (σ y)
       grind)
    | exact resolve eq795 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq879 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq890 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (k X0 (σ y))) ∨ (σ y) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq881 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq881
    | (have j0 := eq881 X0
       grind)
    | exact resolve eq881 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq891 : (M.op (σ x) (σ y)) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq880
    | exact resolve eq880 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq892 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq176 eq886
    | exact resolve eq886 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq896 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq777 eq891
    | exact resolve eq891 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq898 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq896 eq795
    | exact resolve eq795 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq896 eq176
    | exact resolve eq176 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq896 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq900
  have eq903 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq898
  have eq905 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq902
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq902
    | exact resolve eq902 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq906 : (k (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq903
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq903
    | exact resolve eq903 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq915 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq906 eq795
    | exact resolve eq795 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq906 eq176
    | exact resolve eq176 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq919 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq915
  have eq922 : (M.op (σ x) (k (σ x) (σ x))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq916
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq916
    | exact resolve eq916 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq929 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y (k X0 x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op X0 X0) = x ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq845 X0
       have i₂ := eq11 X0 x
       grind)
    | exact superpose eq11 eq845
    | (have j1 := eq11 X0 x
       grind)
    | exact resolve eq845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq941 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y (k X0 x)) ∨ x = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq929 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq929
    | (have j0 := eq929 X0
       grind)
    | exact resolve eq929 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq1012 : (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq919 eq176
    | exact resolve eq176 eq919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1023 : (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) = (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq922 eq892
    | exact resolve eq892 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1026 : (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) = (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1023
  have eq1029 : (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1012 eq1026
    | exact resolve eq1026 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012 eq1026
  have eq1044 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq858
       grind)
    | exact superpose eq858 eq40
    | exact resolve eq40 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq1045 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1044
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1044
    | exact resolve eq1044 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1047 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq1045
    | exact resolve eq1045 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1047 eq905
    | exact resolve eq905 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq1047
  have eq1059 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by grind
  clear eq1055
  have eq1064 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by
    first
    | (have r₁ := eq1059
       have r₂ := eq27
       grind)
    | exact resolve eq1059 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1071 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq1064 eq97
    | exact resolve eq97 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq1064
  have eq1082 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq31 eq1071
    | exact resolve eq1071 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1083 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1082
  have eq1274 : (M.op y y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq876
       have i₂ := eq1083
       grind)
    | exact superpose eq1083 eq876
    | exact resolve eq876 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1275 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq875
       have i₂ := eq1083
       grind)
    | exact superpose eq1083 eq875
    | exact resolve eq875 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq1278 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1083
       grind)
    | exact superpose eq1083 eq39
    | exact resolve eq39 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1280 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq562 x
       have i₂ := eq1083
       grind)
    | exact superpose eq1083 eq562
    | exact resolve eq562 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq1281 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq181 x X0
       have i₂ := eq1083
       grind)
    | exact superpose eq1083 eq181
    | exact resolve eq181 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1282 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1280
  have eq1283 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1275
  have eq1284 : (M.op y y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1274
  have eq1285 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1278
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1278
    | exact resolve eq1278 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq1287 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1283
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1283
    | exact resolve eq1283 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1288 : (k y y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1284
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1284
    | exact resolve eq1284 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1289 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1285
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1285
    | exact resolve eq1285 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1291 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq760 eq1288
    | exact resolve eq1288 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1295 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1282
       grind)
    | exact superpose eq1282 eq40
    | exact resolve eq40 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1300 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1295
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1295
    | exact resolve eq1295 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq1305 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1287 eq41
    | exact resolve eq41 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1307 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1287 eq181
    | exact resolve eq181 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1308 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq1305
    | exact resolve eq1305 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1310 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq922
    | exact resolve eq922 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1311 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq919
    | exact resolve eq919 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq1318 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1289 eq181
    | exact resolve eq181 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1320 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1311
  have eq1321 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1310
  have eq1325 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1320
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq1320
    | exact resolve eq1320 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq1326 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq1321
    | exact resolve eq1321 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1329 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq777 eq1325
    | exact resolve eq1325 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1362 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1308 eq181
    | exact resolve eq181 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1370 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op (σ x) (σ y)) (M.op X0 (σ x))) ∨ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1329 eq711
    | (have j0 := eq711 (M.op (σ x) (σ y)) X0 (σ x)
       grind)
    | exact resolve eq711 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1371 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1329 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq11 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1374 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1371
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq1371
    | exact resolve eq1371 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq1375 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op (σ x) (σ y)) (M.op X0 (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1326 eq1370
    | (have j0 := eq1370 X0
       grind)
    | exact resolve eq1370 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1376 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op (σ x) (σ y)) (M.op X0 (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1375 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1400 : (M.op y y) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1281 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1281
    | (have j0 := eq1281 y
       grind)
    | exact resolve eq1281 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq1425 : (k y y) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1400
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1400
    | exact resolve eq1400 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1437 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq760 eq1425
    | exact resolve eq1425 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq1457 : ∀ X0 : G, (M.op X0 x) = (k (M.op x y) (M.op X0 x)) ∨ (k (M.op x y) (M.op x y)) = (M.op X0 x) ∨ (M.op x y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1437 eq711
    | (have j0 := eq711 (M.op x y) X0 x
       grind)
    | exact resolve eq711 eq1437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437
  have eq1465 : ∀ X0 : G, (M.op X0 x) = (k (M.op x y) (M.op X0 x)) ∨ (M.op x y) = (M.op X0 x) ∨ (M.op x y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1287 eq1457
    | (have j0 := eq1457 X0
       grind)
    | exact resolve eq1457 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287 eq1457
  have eq1466 : ∀ X0 : G, (M.op X0 x) = (k (M.op x y) (M.op X0 x)) ∨ (M.op x y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1465 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1492 : (k x x) = (M.op (M.op x y) (k x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq776 eq1307
    | exact resolve eq1307 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq1307
  have eq1506 : (k x x) = (M.op (M.op x y) (k x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1492
  have eq1514 : y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1083 eq1506
    | exact resolve eq1506 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506
  have eq1532 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) (M.op y X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1514 eq16
    | exact resolve eq16 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1514
  have eq1566 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1318 eq892
    | exact resolve eq892 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1571 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1566 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq1578 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq795 eq1571
    | exact resolve eq1571 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795 eq1571
  have eq1691 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (k X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (k X0 X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1362 eq711
    | (have j0 := eq711 X0 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq711 eq1362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq1693 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (k (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1362 eq11
    | (have j0 := eq11 (M.op (σ (M.op x y)) X0) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq1362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq1697 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (k (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1693 X0
       have j1 := eq12 (M.op (σ (M.op x y)) X0) (k (M.op (σ (M.op x y)) X0) (σ (M.op x y)))
       grind)
    | (have r₁ := eq1693 (σ (M.op x y))
       have r₂ := eq12 (σ (M.op x y)) (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))
       grind)
    | (have r₁ := eq1693 X0
       have r₂ := eq12 (M.op (σ (M.op x y)) X0) (σ (M.op x y))
       grind)
    | (have r₁ := eq1693 (σ (M.op x y))
       have r₂ := eq12 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1693 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq1698 : ∀ X0 : G, (k X0 (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ (M.op x y)) X0) ∨ (k X0 X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1691 X0
       have i₂ := eq174 sF1
       grind)
    | exact superpose eq174 eq1691
    | (have j0 := eq1691 X0
       grind)
    | exact resolve eq1691 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1703 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (k X0 X0) ∨ (k X0 (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ (M.op x y)) X0) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1698 X0
       have i₂ := eq174 sF1
       grind)
    | exact superpose eq174 eq1698
    | (have j0 := eq1698 X0
       grind)
    | exact resolve eq1698 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698
  have eq1706 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = X0 ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k X0 X0) ∨ (k X0 (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1703 X0
       have i₂ := eq174 sF1
       grind)
    | exact superpose eq174 eq1703
    | (have j0 := eq1703 X0
       grind)
    | exact resolve eq1703 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703
  have eq1708 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k X0 X0) ∨ (k X0 (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1308 eq1706
    | (have j0 := eq1706 X0
       grind)
    | exact resolve eq1706 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706
  have eq1710 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (σ (M.op x y)) = (k X0 X0) ∨ (k X0 (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1308 eq1708
    | (have j0 := eq1708 X0
       grind)
    | exact resolve eq1708 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708
  have eq1712 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (k X0 X0) ∨ (σ (M.op x y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1308 eq1710
    | (have j0 := eq1710 X0
       grind)
    | exact resolve eq1710 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710
  have eq1806 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1329 eq1578
    | exact resolve eq1578 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq1818 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1806
  have eq1940 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) (M.op x y)) ∨ (M.op x y) = (M.op (M.op y X0) (M.op y X0)) ∨ (M.op x y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1532 eq11
    | (have j0 := eq11 (M.op y X0) (M.op x y)
       grind)
    | exact resolve eq11 eq1532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532
  have eq1950 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) (M.op x y)) ∨ (M.op x y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1940 X0
       have j1 := eq12 (M.op y X0) (k (M.op y X0) (M.op x y))
       grind)
    | (have r₁ := eq1940 y
       have r₂ := eq12 y (k (M.op y y) (M.op x y))
       grind)
    | (have r₁ := eq1940 X0
       have r₂ := eq12 (M.op y X0) (M.op x y)
       grind)
    | (have r₁ := eq1940 y
       have r₂ := eq12 y (M.op x y)
       grind)
    | exact resolve eq1940 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq2738 : (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1029 eq11
    | (have j0 := eq11 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)
       grind)
    | exact resolve eq11 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq2745 : (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2738
       have i₂ := eq174 (k sF4 sF4)
       grind)
    | exact superpose eq174 eq2738
    | exact resolve eq2738 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2738
  have eq2752 : (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ y) (M.op (σ x) (σ y))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1318 eq2745
    | exact resolve eq2745 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318 eq2745
  have eq2759 : (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (k (σ x) (σ x)) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq906 eq2752
    | exact resolve eq2752 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906 eq2752
  have eq2763 : (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq2759
    | exact resolve eq2759 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759
  have eq2767 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1326 eq2763
    | exact resolve eq2763 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763
  have eq2768 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2767
  have eq2774 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1326 eq2768
    | exact resolve eq2768 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768
  have eq2777 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1326 eq2774
    | exact resolve eq2774 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2774
  have eq2779 : (τ (σ y)) = (k (τ (M.op (σ x) (σ y))) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2777 eq152
    | exact resolve eq152 eq2777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq2777
  have eq2784 : y = (k (τ (M.op (σ x) (σ y))) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31 eq2779
    | exact resolve eq2779 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2779
  have eq3699 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1374 eq1326
    | exact resolve eq1326 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq3704 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3699
  have eq3834 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq899 eq1376
    | exact resolve eq1376 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq1376
  have eq3837 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3834
  have eq3840 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1329 eq3837
    | exact resolve eq3837 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329 eq3837
  have eq3844 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3704 eq3840
    | exact resolve eq3840 eq3704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704 eq3840
  have eq3849 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3844
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq3844
    | exact resolve eq3844 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3844
  have eq3850 : (σ x) = (σ y) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq3849
    | exact resolve eq3849 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3849
  have eq3851 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3850
  have eq3853 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3851 eq141
    | exact resolve eq141 eq3851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq3856 : x = (k (τ (M.op (σ x) (σ y))) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq3853
    | exact resolve eq3853 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3853
  have eq3868 : (k x x) = (k (M.op x y) (k x x)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1466 x
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1466
    | exact resolve eq1466 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq3880 : (M.op x y) = (k x x) ∨ y = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1083 eq3868
    | exact resolve eq3868 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3868
  have eq3888 : (M.op y (M.op x y)) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq876
       have i₂ := eq3880
       grind)
    | exact superpose eq3880 eq876
    | exact resolve eq876 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq3880
  have eq3897 : (M.op y (M.op x y)) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k (M.op x y) y) := by grind
  clear eq3888
  have eq3905 : (k x x) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq859 eq3897
    | exact resolve eq3897 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859 eq3897
  have eq3908 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq1083 eq3905
    | exact resolve eq3905 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083 eq3905
  have eq3911 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq1291 eq3908
    | exact resolve eq3908 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291 eq3908
  have eq3912 : y = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3911
  have eq3913 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3912 eq37
    | exact resolve eq37 eq3912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3912
  have eq3917 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3913
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3913
    | exact resolve eq3913 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3913
  have eq4267 : (k y y) = (k (k y y) (M.op x y)) ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1950 y
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1950
    | exact resolve eq1950 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950
  have eq4287 : (M.op x y) = (k y y) ∨ x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq760 eq4267
    | exact resolve eq4267 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq4267
  have eq4330 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq4287
       grind)
    | exact superpose eq4287 eq40
    | exact resolve eq40 eq4287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4287
  have eq4336 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4330
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4330
    | exact resolve eq4330 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4330
  have eq4341 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq4336
    | exact resolve eq4336 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4336
  have eq4344 : x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq777 eq4341
    | exact resolve eq4341 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4341
  have eq4348 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4344 eq41
    | exact resolve eq41 eq4344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq4344
  have eq4350 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4348
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4348
    | exact resolve eq4348 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4348
  have eq4356 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4350 eq712
    | (have j0 := eq712 (σ x) (σ (M.op x y)) x
       grind)
    | exact resolve eq712 eq4350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq4350
  have eq4357 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq4356 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4356
  have eq4358 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1289 eq4357
    | (have j0 := eq4357 X0
       grind)
    | exact resolve eq4357 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4357
  have eq5734 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq4358
    | (have j0 := eq4358 (σ y)
       grind)
    | exact resolve eq4358 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4358
  have eq5778 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5734 eq1697
    | exact resolve eq1697 eq5734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697 eq5734
  have eq5784 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq5778
  have eq5791 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq5784
       have r₂ := eq27
       grind)
    | exact resolve eq5784 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5784
  have eq6619 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3917 eq890
    | (have j0 := eq890 (σ (M.op x y))
       grind)
    | exact resolve eq890 eq3917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq6655 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq6619
  have eq6664 : (k (σ y) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq6655
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq6655
    | exact resolve eq6655 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6655
  have eq6669 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq777 eq6664
    | exact resolve eq6664 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6664
  have eq6673 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1308 eq6669
    | exact resolve eq6669 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308 eq6669
  have eq6674 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6673
  have eq6677 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6674 eq892
    | exact resolve eq892 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq6699 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq6677
  have eq6708 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq896 eq6699
    | exact resolve eq6699 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq6699
  have eq6937 : (M.op y x) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3856 eq941
    | (have j0 := eq941 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq941 eq3856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq3856
  have eq6971 : (M.op y x) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq6937
  have eq6981 : x = (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op y x) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq6971
       have i₂ := eq404 sF4 sF4
       grind)
    | exact superpose eq404 eq6971
    | exact resolve eq6971 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6971
  have eq6988 : x = (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq849 eq6981
    | exact resolve eq6981 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849 eq6981
  have eq6992 : x = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1326 eq6988
    | exact resolve eq6988 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6988
  have eq6993 : (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6992
  have eq7003 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6993 eq11
    | (have j0 := eq11 (τ (M.op (σ x) (σ y))) (M.op x y)
       grind)
    | exact resolve eq11 eq6993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6993
  have eq7011 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq7003
       have i₂ := eq174 (τ sF4)
       grind)
    | exact superpose eq174 eq7003
    | exact resolve eq7003 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7003
  have eq7020 : (M.op x y) = (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq7011
       have i₂ := eq404 sF4 sF4
       grind)
    | exact superpose eq404 eq7011
    | exact resolve eq7011 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq7011
  have eq7028 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1326 eq7020
    | exact resolve eq7020 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7020
  have eq7029 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7028
  have eq7221 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7029 eq34
    | exact resolve eq34 eq7029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq7029
  have eq7228 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq7221
    | exact resolve eq7221 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7221
  have eq7322 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6674 eq182
    | exact resolve eq182 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6674
  have eq7352 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq6708 eq182
    | exact resolve eq182 eq6708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6708
  have eq7755 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1326 eq7352
    | exact resolve eq7352 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7352
  have eq7782 : (σ y) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq7322
    | exact resolve eq7322 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7322
  have eq8499 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ x)) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7782 eq182
    | exact resolve eq182 eq7782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7782
  have eq8522 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8499
       have i₂ := eq16 sF1 sF2 sF3
       grind)
    | exact superpose eq16 eq8499
    | exact resolve eq8499 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8499
  have eq8540 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq8522
    | exact resolve eq8522 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8522
  have eq8552 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq777 eq8540
    | exact resolve eq8540 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8540
  have eq8580 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1712 eq7755
    | (have j1 := eq1712 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq7755 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7755
  have eq8612 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq8580
  have eq8629 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq8612
       have r₂ := eq27
       grind)
    | exact resolve eq8612 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8612
  have eq8638 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1326 eq8629
    | exact resolve eq8629 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8629
  have eq8646 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq8638
       have r₂ := eq27
       grind)
    | exact resolve eq8638 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8638
  have eq8884 : (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1712 eq8552
    | (have j1 := eq1712 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq8552 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712 eq8552
  have eq8923 : (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq8884
  have eq8937 : (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq8923
       have r₂ := eq27
       grind)
    | exact resolve eq8923 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8923
  have eq8946 : (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1326 eq8937
    | exact resolve eq8937 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8937
  have eq8952 : (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq8946
       have r₂ := eq27
       grind)
    | exact resolve eq8946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8946
  have eq8974 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8646 eq182
    | exact resolve eq182 eq8646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8646
  have eq8988 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1326 eq8974
    | exact resolve eq8974 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8974
  have eq9283 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8952 eq182
    | exact resolve eq182 eq8952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8952
  have eq9301 : (σ y) = (M.op (σ x) (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq9283
    | exact resolve eq9283 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9283
  have eq9986 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq8988
       have i₂ := eq11 sF4 (k sF4 sF1)
       grind)
    | exact superpose eq11 eq8988
    | (have j1 := eq11 (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y)))
       grind)
    | exact resolve eq8988 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8988
  have eq10019 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq9986
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq9986
    | exact resolve eq9986 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9986
  have eq10026 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1326 eq10019
    | exact resolve eq10019 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10019
  have eq10027 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10026
  have eq10032 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5791 eq10027
    | exact resolve eq10027 eq5791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10027
  have eq10036 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3851 eq10032
    | exact resolve eq10032 eq3851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10032
  have eq10038 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3851 eq10036
    | exact resolve eq10036 eq3851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851 eq10036
  have eq10039 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1818 eq10038
    | exact resolve eq10038 eq1818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818 eq10038
  have eq10084 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (σ x)) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9301 eq182
    | exact resolve eq182 eq9301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq9301
  have eq10104 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10084
       have i₂ := eq16 (k sF4 sF1) sF2 sF3
       grind)
    | exact superpose eq16 eq10084
    | exact resolve eq10084 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10084
  have eq10116 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq10104
    | exact resolve eq10104 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10104
  have eq10126 : (σ x) = (M.op (σ x) (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq777 eq10116
    | exact resolve eq10116 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10116
  have eq10746 : (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10126
       have i₂ := eq11 sF4 (k sF4 sF1)
       grind)
    | exact superpose eq11 eq10126
    | (have j1 := eq11 (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y)))
       grind)
    | exact resolve eq10126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10126
  have eq10790 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10746
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq10746
    | exact resolve eq10746 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10746
  have eq10801 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1326 eq10790
    | exact resolve eq10790 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326 eq10790
  have eq10802 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10801
  have eq10810 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (k (σ x) (k (σ x) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10039 eq10802
    | exact resolve eq10802 eq10039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10039 eq10802
  have eq10816 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (k (σ x) (k (σ x) (σ x)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5791 eq10810
    | exact resolve eq10810 eq5791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5791 eq10810
  have eq10820 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (k (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq10816
    | exact resolve eq10816 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10816
  have eq10823 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1300 eq10820
    | exact resolve eq10820 eq1300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300 eq10820
  have eq10825 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10823
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq10823
    | exact resolve eq10823 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10823
  have eq10826 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq10825
    | exact resolve eq10825 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289 eq10825
  have eq10827 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq10826
  have eq10829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10827 eq7228
    | exact resolve eq7228 eq10827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7228 eq10827
  have eq10850 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10829
  have eq10860 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq10850
       have r₂ := eq27
       grind)
    | exact resolve eq10850 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10850
  have eq10925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10860 eq14
    | exact resolve eq14 eq10860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10860
  have eq10968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq10925
    | exact resolve eq10925 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10925
  have eq10986 : x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq10968
       have r₂ := eq27
       grind)
    | exact resolve eq10968 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10968
  have eq11001 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10986 eq2784
    | exact resolve eq2784 eq10986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784
  have eq11014 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10986 eq14
    | exact resolve eq14 eq10986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10986
  have eq11034 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq11001
  have eq11040 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11014
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11014
    | exact resolve eq11014 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11014
  have eq11044 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1282 eq11034
    | exact resolve eq11034 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282 eq11034
  have eq11045 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq11044
  have eq11050 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11040 eq11045
    | exact resolve eq11045 eq11040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11040 eq11045
  have eq11051 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq11050
  have eq11053 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11051 eq31
    | exact resolve eq31 eq11051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11051
  have eq11088 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq11053
    | exact resolve eq11053 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11053
  have eq11089 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq11088
  have eq11117 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq11089 eq3917
    | exact resolve eq3917 eq11089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3917 eq11089
  have eq11136 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11117
  have eq11150 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq777 eq11136
    | exact resolve eq11136 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq11136
  have eq11151 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq11150
  have eq11180 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq11151 eq31
    | exact resolve eq31 eq11151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq11151
  have eq11216 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq11180
    | exact resolve eq11180 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11180
  have eq11217 : x = y := by grind
  clear eq11216
  have eq11235 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11217
       grind)
    | exact superpose eq11217 eq18
    | exact resolve eq18 eq11217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq11236 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq11217
       grind)
    | exact superpose eq11217 eq24
    | exact resolve eq24 eq11217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq11217
  have eq11244 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11236
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11236
    | exact resolve eq11236 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11236
  have eq11245 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq11235
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq11235
    | exact resolve eq11235 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11235
  have eq11246 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11244 eq26
    | exact resolve eq26 eq11244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq11244
  have eq11282 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq11246
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq11246
    | exact resolve eq11246 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq11246
  have eq11291 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq11245
       grind)
    | exact superpose eq11245 eq39
    | exact resolve eq39 eq11245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq11245
  have eq11295 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq11291
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11291
    | exact resolve eq11291 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq11291
  have eq11300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11282 eq11295
    | exact resolve eq11295 eq11282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11282 eq11295
  have eq11302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq11300
    | exact resolve eq11300 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq11300
  have eq11304 : False := by grind
  exact eq11304

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_x_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq37 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23 (σ X0)
       grind)
    | exact superpose eq23 eq15
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq40
    | exact resolve eq40 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq40
  have eq64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq37 (σ X1) (σ X0)
       grind)
    | exact superpose eq37 eq15
    | (have j1 := eq37 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq64
    | (have j0 := eq64 X0 X1
       have j1 := eq37 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq64 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq64
  have eq9239 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq644 x y
       grind)
    | exact superpose eq644 eq16
    | (have j1 := eq644 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq644 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq644 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq644 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq9325 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq9239
  have eq10485 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9325
       grind)
    | exact superpose eq9325 eq10
    | exact resolve eq10 eq9325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9325
  have eq10552 : x = y ∨ x = y := by
    first
    | (have i₁ := eq10485
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10485
    | exact resolve eq10485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10485
  have eq10553 : x = y := by grind
  clear eq10552
  have eq13491 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10553
       grind)
    | exact superpose eq10553 eq16
    | exact resolve eq16 eq10553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10553
  have eq13492 : False := by grind
  exact eq13492
