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
