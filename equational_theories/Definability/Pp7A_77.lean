import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq72 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq16
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq69
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq109
    | exact resolve eq109 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq631 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq11014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11015 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11014
    | exact resolve eq11014 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11014
  have eq11026 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq11015
       have r₂ := eq28
       grind)
    | exact resolve eq11015 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11015
  have eq11028 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11026
    | exact resolve eq11026 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11026
  have eq11030 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq11028
  have eq11046 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11030
    | exact resolve eq11030 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11030
  have eq11055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11046 eq111
    | exact resolve eq111 eq11046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11046
  have eq11067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11055
  have eq11069 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11067
       have r₂ := eq28
       grind)
    | exact resolve eq11067 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11067
  have eq11185 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11069
  have eq11201 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11185
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11185
    | exact resolve eq11185 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11185
  have eq11207 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq11201
       grind)
    | exact superpose eq11201 eq69
    | exact resolve eq69 eq11201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11201
  have eq11229 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11207
    | exact resolve eq11207 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11207
  have eq11389 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11229 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq11229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11389
    | exact resolve eq11389 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11389
  have eq11403 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11392
       have r₂ := eq28
       grind)
    | exact resolve eq11392 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11392
  have eq11405 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11403
    | exact resolve eq11403 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11403
  have eq11406 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11405
  have eq11409 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11406
  have eq11425 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq11409
    | exact resolve eq11409 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11409
  have eq11555 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11425 eq11229
    | exact resolve eq11229 eq11425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11229 eq11425
  have eq11561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11555
  have eq11565 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11561
       have r₂ := eq28
       grind)
    | exact resolve eq11561 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11561
  have eq11567 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11565 eq28
    | exact resolve eq28 eq11565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11569 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11565 eq73
    | (have r₁ := eq73
       have r₂ := eq11565
       grind)
    | exact resolve eq73 eq11565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq11574 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq11569
  have eq11812 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq11574
  have eq11828 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq11812
    | exact resolve eq11812 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11812
  have eq11948 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq111 eq11828
    | exact resolve eq11828 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq11966 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq11828
  have eq11970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq11948
  have eq11972 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11966
       have r₂ := eq11565
       grind)
    | exact resolve eq11966 eq11565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11565 eq11966
  have eq11974 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq11970
       have r₂ := eq11567
       grind)
    | exact resolve eq11970 eq11567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11567 eq11970
  have eq11976 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11974
       have r₂ := eq28
       grind)
    | exact resolve eq11974 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11974
  have eq11985 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11972 eq80
    | exact resolve eq80 eq11972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq11972
  have eq12022 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq11985
    | exact resolve eq11985 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11985
  have eq12029 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq11976
  have eq12045 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12029
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12029
    | exact resolve eq12029 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12029
  have eq12166 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12022
       have i₂ := eq12045
       grind)
    | exact superpose eq12045 eq12022
    | exact resolve eq12022 eq12045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12022 eq12045
  have eq12172 : x = (M.op x y) := by grind
  clear eq12166
  have eq12200 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq12172 eq21
    | exact resolve eq21 eq12172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq12206 : x ≠ x ∨ y = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq12172 eq72
    | (have r₁ := eq72
       have r₂ := eq12172
       grind)
    | exact resolve eq72 eq12172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq12258 : y = (M.op x x) ∨ x = (k y x) := by grind
  clear eq12206
  have eq12309 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12200
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12200
    | exact resolve eq12200 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12200
  have eq12311 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12309 eq27
    | exact resolve eq27 eq12309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12471 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq12258
  have eq12487 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12471
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12471
    | exact resolve eq12471 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq12471
  have eq12496 : x = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq12172 eq12487
    | exact resolve eq12487 eq12172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12172 eq12487
  have eq12497 : x = (k y x) := by grind
  clear eq12496
  have eq12509 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq12497
       grind)
    | exact superpose eq12497 eq69
    | exact resolve eq69 eq12497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq12521 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq631 x y
       have i₂ := eq12497
       grind)
    | exact superpose eq12497 eq631
    | (have j0 := eq631 x y
       grind)
    | exact resolve eq631 eq12497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq12497
  have eq12524 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq12521
  have eq12531 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12524
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12524
    | exact resolve eq12524 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12524
  have eq12541 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq12309 eq12509
    | exact resolve eq12509 eq12309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12509
  have eq12543 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12531
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12531
    | exact resolve eq12531 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12531
  have eq12553 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq12541
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12541
    | exact resolve eq12541 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12541
  have eq12554 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12543
    | exact resolve eq12543 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq12543
  have eq12563 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq12309 eq12553
    | exact resolve eq12553 eq12309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12553
  have eq12564 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12309 eq12554
    | exact resolve eq12554 eq12309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12554
  have eq12568 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq12564
       have r₂ := eq28
       grind)
    | exact resolve eq12564 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12564
  have eq12572 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12568
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12568
    | exact resolve eq12568 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq12568
  have eq12576 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12309 eq12572
    | exact resolve eq12572 eq12309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12309 eq12572
  have eq12580 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq12576
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12576
    | exact resolve eq12576 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq12576
  have eq12647 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq12580
  have eq12663 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq12311 eq12647
    | exact resolve eq12647 eq12311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12311 eq12647
  have eq12667 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12563 eq12663
    | exact resolve eq12663 eq12563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12563 eq12663
  have eq12668 : False := by grind
  exact eq12668

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq22
  have eq263 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) ≠ (M.op X2 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq13 X2 X0
       grind)
    | exact superpose eq13 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq13 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq263 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq1156 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq264 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1210 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1156 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1211 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1210 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1347 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq1211 (τ X0)
       grind)
    | exact superpose eq1211 eq31
    | exact resolve eq31 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1386 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1347 X0
       have i₂ := eq1211 X0
       grind)
    | exact superpose eq1211 eq1347
    | exact resolve eq1347 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211 eq1347
  have eq1538 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq1386 X0
       grind)
    | exact superpose eq1386 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq1386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1540 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq1386 X0
       grind)
    | exact superpose eq1386 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq1386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq1543 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1538 X0 X1
       have j1 := eq1540 X0 X1
       grind)
    | (have r₁ := eq1538 X0 X1
       have r₂ := eq1540 X0 X1
       grind)
    | exact resolve eq1538 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538 eq1540
  have eq1656 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1543 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1543
    | exact resolve eq1543 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1674 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq264 X0 X1 X1
       have i₂ := eq1656 X0 X1
       grind)
    | (have i₁ := eq264 X1 X1 X0
       have i₂ := eq1656 X0 X1
       grind)
    | exact superpose eq1656 eq264
    | (have j0 := eq264 X0 X2 X2
       have j1 := eq1656 X0 X2
       grind)
    | (have r₁ := eq264 X1 X1 X0
       have r₂ := eq1656 X0 X1
       grind)
    | (have r₁ := eq264 X0 X1 X1
       have r₂ := eq1656 X0 X1
       grind)
    | exact resolve eq264 eq1656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq1656
  have eq1683 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1674 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq1684 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1683 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683
  have eq1753 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1684 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq1754 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1753 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq1783 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1754 (σ X1) (σ X0)
       grind)
    | exact superpose eq1754 eq15
    | exact resolve eq15 eq1754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1862 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1783 X0 X1
       have i₂ := eq1754 X1 X0
       grind)
    | exact superpose eq1754 eq1783
    | exact resolve eq1783 eq1754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1754 eq1783
  have eq2706 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1862 x y
       grind)
    | exact superpose eq1862 eq16
    | (have r₁ := eq16
       have r₂ := eq1862 x y
       grind)
    | exact resolve eq16 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq2721 : False := by grind
  exact eq2721

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pyy_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq265 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq268 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq266 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq279 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq268 (σ X0)
       grind)
    | exact superpose eq268 eq15
    | exact resolve eq15 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq279
    | exact resolve eq279 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq279
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq345 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       have j1 := eq344 X0 X1
       grind)
    | (have r₁ := eq343 X0 X1
       have r₂ := eq344 X0 X1
       grind)
    | exact resolve eq343 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq344
  have eq385 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq345 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq345
    | exact resolve eq345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq419 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq385 X0 X1
       grind)
    | exact superpose eq385 eq9
    | (have j1 := eq385 X0 X1
       grind)
    | exact resolve eq9 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq566 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq419 X0 X1
       grind)
    | exact superpose eq419 eq9
    | (have j1 := eq419 X0 X1
       grind)
    | exact resolve eq9 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq571 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq566 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq566 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq566 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq616 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq571 (σ X0) (σ X1)
       grind)
    | exact superpose eq571 eq15
    | exact resolve eq15 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq616 X0 X1
       have i₂ := eq571 X0 X1
       grind)
    | exact superpose eq571 eq616
    | exact resolve eq616 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq616
  have eq959 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq643 x y
       grind)
    | exact superpose eq643 eq16
    | (have r₁ := eq16
       have r₂ := eq643 x y
       grind)
    | exact resolve eq16 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq975 : False := by grind
  exact eq975

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_x_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq265 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq268 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq266 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq279 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq268 (σ X0)
       grind)
    | exact superpose eq268 eq15
    | exact resolve eq15 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq279
    | exact resolve eq279 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq279
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq345 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       have j1 := eq344 X0 X1
       grind)
    | (have r₁ := eq343 X0 X1
       have r₂ := eq344 X0 X1
       grind)
    | exact resolve eq343 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq344
  have eq385 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq345 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq345
    | exact resolve eq345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq418 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq385 X0 X1
       grind)
    | exact superpose eq385 eq9
    | (have j1 := eq385 X0 X1
       grind)
    | exact resolve eq9 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq652 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq418 X0 X1
       grind)
    | exact superpose eq418 eq9
    | (have j1 := eq418 X0 X1
       grind)
    | exact resolve eq9 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq658 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq652 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq652 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq652 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq673 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq658 (σ X0) (σ X1)
       grind)
    | exact superpose eq658 eq15
    | exact resolve eq15 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq673 X0 X1
       have i₂ := eq658 X0 X1
       grind)
    | exact superpose eq658 eq673
    | exact resolve eq673 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq673
  have eq1018 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq700 x y
       grind)
    | exact superpose eq700 eq16
    | (have r₁ := eq16
       have r₂ := eq700 x y
       grind)
    | exact resolve eq16 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq1034 : False := by grind
  exact eq1034

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pyx_pyy_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq64 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq64 (M.op X0 X1)
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq64 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq64
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq413 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq425 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq424 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq432 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq425 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq425
    | (have j0 := eq425 X0 X1
       grind)
    | exact resolve eq425 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq434 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq411
       have i₂ := eq64 (σ x)
       grind)
    | exact superpose eq64 eq411
    | exact resolve eq411 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq435 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq410 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq410
    | (have j0 := eq410 X0 X1
       grind)
    | exact resolve eq410 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq445 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq432 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq432
    | (have j0 := eq432 X0 X1
       grind)
    | exact resolve eq432 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq448 : (σ x) = (σ y) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq434
       have i₂ := eq64 (σ y)
       grind)
    | exact superpose eq64 eq434
    | exact resolve eq434 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq452 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq448
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq448
    | exact resolve eq448 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq455 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq445 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq445
    | (have j0 := eq445 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq445 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq445 (τ X0) X1
       grind)
    | exact superpose eq445 eq18
    | (have j1 := eq445 (τ X0) X1
       grind)
    | exact resolve eq18 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq445
  have eq679 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (τ X0) = (τ X1) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (τ X1)
       have i₂ := eq478 X1 (τ X0)
       grind)
    | exact superpose eq478 eq19
    | (have j1 := eq478 X0 (τ X1)
       grind)
    | exact resolve eq19 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq478
  have eq685 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (τ X0) = (τ X1) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq679 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq679
    | (have j0 := eq679 X0 X1
       grind)
    | exact resolve eq679 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq696 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ X0) = (τ X1) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq685 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq685
    | (have j0 := eq685 X0 X1
       grind)
    | exact resolve eq685 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq697 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X1 X0) = X0 ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq696 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq696
    | (have j0 := eq696 X0 X1
       grind)
    | exact resolve eq696 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq2139 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k (σ X0) X1) = X1 ∨ (τ X1) = X0 := by
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
  have eq3311 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2139 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2139
    | (have j0 := eq2139 X1 (σ X0)
       grind)
    | exact resolve eq2139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2139
  have eq3355 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3311 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3311
    | (have j0 := eq3311 X0 X1
       grind)
    | exact resolve eq3311 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311
  have eq3358 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3355 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3355
    | (have j0 := eq3355 X0 X1
       grind)
    | exact resolve eq3355 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355
  have eq3687 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3358 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3861 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq452
       have i₂ := eq435 x y
       grind)
    | exact superpose eq435 eq452
    | (have j1 := eq435 x y
       grind)
    | (have r₁ := eq452
       have r₂ := eq435 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq452
       have r₂ := eq435 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq452 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq3863 : x = y ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by grind
  clear eq3861
  have eq13492 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq455 x y
       grind)
    | exact superpose eq455 eq16
    | (have j1 := eq455 x y
       grind)
    | exact resolve eq16 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq14065 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq13492
       have i₂ := eq3358 y x
       grind)
    | exact superpose eq3358 eq13492
    | (have j1 := eq3358 y x
       grind)
    | (have r₁ := eq13492
       have r₂ := eq3358 y x
       grind)
    | (have r₁ := eq13492
       have r₂ := eq3358 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq13492
       have r₂ := eq3358 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq13492 eq3358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358 eq13492
  have eq14068 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = y := by grind
  clear eq14065
  have eq14070 : x = y ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq3687 x y
       grind)
    | (have r₁ := eq14068
       have r₂ := eq3687 x y
       grind)
    | exact resolve eq14068 eq3687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3687 eq14068
  have eq14071 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14070
       grind)
    | exact superpose eq14070 eq16
    | exact resolve eq16 eq14070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14070
  have eq14072 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14071
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq14071
    | exact resolve eq14071 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14071
  have eq14073 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq14072
       have r₂ := eq64 (σ x)
       grind)
    | exact resolve eq14072 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14072
  have eq14075 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14073
       grind)
    | exact superpose eq14073 eq10
    | exact resolve eq10 eq14073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14073
  have eq14127 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq14075
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14075
    | exact resolve eq14075 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14075
  have eq14172 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14127
       grind)
    | exact superpose eq14127 eq16
    | exact resolve eq16 eq14127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14127
  have eq14173 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq14172
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq14172
    | exact resolve eq14172 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14172
  have eq14174 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq14173
       have r₂ := eq64 (σ x)
       grind)
    | exact resolve eq14173 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14173
  have eq14185 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq14174
       grind)
    | exact superpose eq14174 eq10
    | exact resolve eq10 eq14174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14237 : y = (k x y) := by
    first
    | (have i₁ := eq14185
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq14185
    | exact resolve eq14185 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14185
  have eq126350 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3863
       grind)
    | exact superpose eq3863 eq16
    | exact resolve eq16 eq3863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3863
  have eq126428 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq126350
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq126350
    | exact resolve eq126350 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126350
  have eq126438 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq126428
       have r₂ := eq64 (σ x)
       grind)
    | exact resolve eq126428 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126428
  have eq126439 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq126438
       have i₂ := eq14174
       grind)
    | exact superpose eq14174 eq126438
    | exact resolve eq126438 eq14174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126438
  have eq126440 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq126439
       have i₂ := eq14237
       grind)
    | exact superpose eq14237 eq126439
    | exact resolve eq126439 eq14237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14237 eq126439
  have eq126453 : x = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq67 x y
       have i₂ := eq126440
       grind)
    | exact superpose eq126440 eq67
    | exact resolve eq67 eq126440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126528 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq126453
       have i₂ := eq126440
       grind)
    | exact superpose eq126440 eq126453
    | exact resolve eq126453 eq126440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126440 eq126453
  have eq126601 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq126528
  have eq126625 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq452
       have i₂ := eq126601
       grind)
    | exact superpose eq126601 eq452
    | exact resolve eq452 eq126601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq126601
  have eq126687 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq126625
  have eq126688 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq126687
  have eq126700 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq126688
       have i₂ := eq14174
       grind)
    | exact superpose eq14174 eq126688
    | exact resolve eq126688 eq14174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14174 eq126688
  have eq126701 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq126700
  have eq126745 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq67 (σ x) (σ y)
       have i₂ := eq126701
       grind)
    | exact superpose eq126701 eq67
    | exact resolve eq67 eq126701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq127400 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq126745
       have i₂ := eq126701
       grind)
    | exact superpose eq126701 eq126745
    | exact resolve eq126745 eq126701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126745
  have eq127501 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq127400
  have eq127542 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq126701
       have i₂ := eq127501
       grind)
    | exact superpose eq127501 eq126701
    | exact resolve eq126701 eq127501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126701 eq127501
  have eq127687 : (σ x) = (σ y) := by grind
  clear eq127542
  have eq127754 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq127687
       grind)
    | exact superpose eq127687 eq16
    | exact resolve eq16 eq127687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127758 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq127687
       grind)
    | exact superpose eq127687 eq10
    | exact resolve eq10 eq127687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127687
  have eq127874 : x = y := by
    first
    | (have i₁ := eq127758
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq127758
    | exact resolve eq127758 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127758
  have eq127875 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq127754
       have i₂ := eq64 (σ x)
       grind)
    | exact superpose eq64 eq127754
    | exact resolve eq127754 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127754
  have eq127876 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq127875
       have i₂ := eq127874
       grind)
    | exact superpose eq127874 eq127875
    | exact resolve eq127875 eq127874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127874 eq127875
  have eq127877 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq127876
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq127876
    | exact resolve eq127876 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq127876
  have eq127878 : False := by grind
  exact eq127878

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxx_pyy_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq22 (M.op X0 X1)
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq41 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq40
    | exact resolve eq40 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq94 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq102 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq110 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq115 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 X1
       have i₂ := eq22 (τ X1)
       grind)
    | exact superpose eq22 eq110
    | (have j0 := eq110 X0 X1
       grind)
    | exact resolve eq110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq22 (σ X1)
       grind)
    | exact superpose eq22 eq108
    | (have j0 := eq108 X0 X1
       grind)
    | exact resolve eq108 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq118 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq94
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq102
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq102 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq143 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq135
    | (have j0 := eq135 X0 X1
       grind)
    | exact resolve eq135 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq146 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq116 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq116
    | exact resolve eq116 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq146
    | (have j0 := eq146 X0 X1
       grind)
    | exact resolve eq146 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq507 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq160 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq160
    | exact resolve eq160 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq629 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq115 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq115
    | exact resolve eq115 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq664 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq629
    | (have j0 := eq629 X0 X1
       grind)
    | exact resolve eq629 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq4100 : (σ (M.op x y)) ≠ (σ x) ∨ (k x (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq143 x (σ y)
       grind)
    | exact superpose eq143 eq16
    | (have j1 := eq143 x (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq143 (M.op x y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq16 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4102 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq143 X0 X1
       grind)
    | exact superpose eq143 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq143 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq143 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq143 X0 (M.op (σ X0) X1)
       grind)
    | exact resolve eq13 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq4121 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4102
  have eq4128 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4121 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq4121
    | (have j0 := eq4121 X0 X1
       grind)
    | exact resolve eq4121 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4121
  have eq4129 : (σ (M.op x y)) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4100
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4100
    | exact resolve eq4100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4100
  have eq4133 : ∀ X0 X1 : G, (σ X0) = X1 ∨ (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4128 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq4128
    | (have j0 := eq4128 X0 X1
       grind)
    | exact resolve eq4128 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4128
  have eq4134 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4133
  have eq4583 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4134 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4134
    | exact resolve eq4134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4630 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq94 (σ X1) X0
       have i₂ := eq4134 X1 (σ X0)
       grind)
    | exact superpose eq4134 eq94
    | (have j1 := eq4134 X0 (σ X1)
       grind)
    | exact resolve eq94 eq4134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq4134
  have eq4692 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4630 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4630
    | (have j0 := eq4630 X0 X1
       grind)
    | exact resolve eq4630 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4630
  have eq4701 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4583 X0 X1
       have i₂ := eq118 X1 X0
       grind)
    | exact superpose eq118 eq4583
    | (have j0 := eq4583 X0 X1
       grind)
    | exact resolve eq4583 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq4583
  have eq4724 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4692 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4692
    | (have j0 := eq4692 X0 X1
       grind)
    | exact resolve eq4692 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4692
  have eq4731 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4724 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4724
    | (have j0 := eq4724 X0 X1
       grind)
    | exact resolve eq4724 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4724
  have eq4804 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq4701 X0 X1
       grind)
    | exact superpose eq4701 eq11
    | (have j1 := eq4701 X0 X1
       grind)
    | exact resolve eq11 eq4701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4701
  have eq4912 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4804 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4804
    | (have j0 := eq4804 X0 X1
       grind)
    | exact resolve eq4804 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4804
  have eq4982 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq4912 (τ X0) X1
       grind)
    | exact superpose eq4912 eq18
    | (have j1 := eq4912 (τ X0) X1
       grind)
    | exact resolve eq18 eq4912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4912
  have eq5891 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4731 X1 X0
       grind)
    | exact superpose eq4731 eq11
    | (have j1 := eq4731 X1 X0
       grind)
    | exact resolve eq11 eq4731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4731
  have eq6807 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5891 x y
       grind)
    | exact superpose eq5891 eq16
    | (have j1 := eq5891 x y
       grind)
    | exact resolve eq16 eq5891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5891
  have eq6919 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6807
       have i₂ := eq507 y x
       grind)
    | exact superpose eq507 eq6807
    | (have j1 := eq507 y (M.op x y)
       grind)
    | (have r₁ := eq6807
       have r₂ := eq507 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6807
       have r₂ := eq507 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6807 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507 eq6807
  have eq6924 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6919
  have eq6952 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6924
       grind)
    | exact superpose eq6924 eq16
    | exact resolve eq16 eq6924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6924
  have eq6953 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6952
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq6952
    | exact resolve eq6952 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6952
  have eq6954 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6953
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq6953
    | exact resolve eq6953 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6953
  have eq6955 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq6954
  have eq7189 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq25 x y
       have i₂ := eq6955
       grind)
    | exact superpose eq6955 eq25
    | exact resolve eq25 eq6955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7199 : x ≠ y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  have eq7365 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7189
       have i₂ := eq6955
       grind)
    | exact superpose eq6955 eq7189
    | exact resolve eq7189 eq6955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6955 eq7189
  have eq7384 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7365
  have eq7388 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7384
       have r₂ := eq7199
       grind)
    | exact resolve eq7384 eq7199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7199 eq7384
  have eq8408 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4982 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4982
    | exact resolve eq4982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4982
  have eq8530 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8408 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8408
    | (have j0 := eq8408 X0 X1
       grind)
    | exact resolve eq8408 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8408
  have eq38101 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4129
       have i₂ := eq7388
       grind)
    | exact superpose eq7388 eq4129
    | exact resolve eq4129 eq7388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4129 eq7388
  have eq38107 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq38101
  have eq38108 : (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq38107
  have eq38116 : y = (τ (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq38108
       grind)
    | exact superpose eq38108 eq10
    | exact resolve eq10 eq38108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38108
  have eq38222 : x = y ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38116
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq38116
    | exact resolve eq38116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38116
  have eq38504 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38222
       grind)
    | exact superpose eq38222 eq16
    | exact resolve eq16 eq38222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38222
  have eq38505 : (σ x) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38504
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq38504
    | exact resolve eq38504 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38504
  have eq38506 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38505
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq38505
    | exact resolve eq38505 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38505
  have eq38507 : (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq38506
  have eq38534 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq38507
       grind)
    | exact superpose eq38507 eq11
    | exact resolve eq11 eq38507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38507
  have eq38957 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38534
       grind)
    | exact superpose eq38534 eq16
    | exact resolve eq16 eq38534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38986 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) := by
    first
    | (have i₁ := eq25 (σ x) (σ y)
       have i₂ := eq38534
       grind)
    | exact superpose eq38534 eq25
    | exact resolve eq25 eq38534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq39098 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq38957
       have i₂ := eq8530 x y
       grind)
    | exact superpose eq8530 eq38957
    | (have j1 := eq8530 x y
       grind)
    | (have r₁ := eq38957
       have r₂ := eq8530 x y
       grind)
    | (have r₁ := eq38957
       have r₂ := eq8530 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq38957
       have r₂ := eq8530 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq38957 eq8530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8530
  have eq39099 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38957
       have i₂ := eq664 y x
       grind)
    | exact superpose eq664 eq38957
    | (have j1 := eq664 x y
       grind)
    | (have r₁ := eq38957
       have r₂ := eq664 y x
       grind)
    | (have r₁ := eq38957
       have r₂ := eq664 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq38957
       have r₂ := eq664 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq38957 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq39100 : x = y ∨ x = (M.op x y) := by grind
  clear eq39099
  have eq39101 : x = y ∨ y = (k x y) := by grind
  clear eq39098
  have eq39367 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38957
       have i₂ := eq39100
       grind)
    | exact superpose eq39100 eq38957
    | exact resolve eq38957 eq39100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39100
  have eq39368 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39367
       have i₂ := eq41 x
       grind)
    | exact superpose eq41 eq39367
    | exact resolve eq39367 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39367
  have eq39372 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39368
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq39368
    | exact resolve eq39368 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39368
  have eq39373 : x = (M.op x y) := by grind
  clear eq39372
  have eq39763 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq38957
       have i₂ := eq39101
       grind)
    | exact superpose eq39101 eq38957
    | exact resolve eq38957 eq39101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39101
  have eq39767 : (σ x) ≠ (σ (M.op x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39763
       have i₂ := eq41 x
       grind)
    | exact superpose eq41 eq39763
    | exact resolve eq39763 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq39763
  have eq39771 : (σ x) ≠ (σ x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39767
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq39767
    | exact resolve eq39767 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq39767
  have eq39772 : y = (k x y) := by grind
  clear eq39771
  have eq40242 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq38957
       have i₂ := eq39772
       grind)
    | exact superpose eq39772 eq38957
    | exact resolve eq38957 eq39772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38957
  have eq40282 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq40242
       have i₂ := eq39373
       grind)
    | exact superpose eq39373 eq40242
    | exact resolve eq40242 eq39373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39373 eq40242
  have eq41081 : (σ x) = (M.op (σ x) (σ (k x (k x y)))) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (k x y))) := by
    first
    | (have i₁ := eq38986
       have i₂ := eq116 x (k x y)
       grind)
    | exact superpose eq116 eq38986
    | (have j1 := eq116 x (k x y)
       grind)
    | exact resolve eq38986 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq38986
  have eq41144 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (k x y))) := by
    first
    | (have i₁ := eq41081
       have i₂ := eq39772
       grind)
    | exact superpose eq39772 eq41081
    | exact resolve eq41081 eq39772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41081
  have eq41145 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq41144
  have eq41161 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq41145
       have i₂ := eq39772
       grind)
    | exact superpose eq39772 eq41145
    | exact resolve eq41145 eq39772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41145
  have eq41173 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq41161
       have i₂ := eq38534
       grind)
    | exact superpose eq38534 eq41161
    | exact resolve eq41161 eq38534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38534 eq41161
  have eq41174 : (σ x) = (σ (k x y)) := by grind
  clear eq41173
  have eq41182 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq41174
       have i₂ := eq39772
       grind)
    | exact superpose eq39772 eq41174
    | exact resolve eq41174 eq39772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39772 eq41174
  have eq41188 : False := by grind
  exact eq41188

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_pyy_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq22 (M.op X0 X1)
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq34
    | exact resolve eq34 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq70 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq79 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq90 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq22 (σ X1)
       grind)
    | exact superpose eq22 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq97 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq22 (τ X1)
       grind)
    | exact superpose eq22 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq99 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq70
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq79
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq79 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq129 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq121
    | (have j0 := eq121 X0 X1
       grind)
    | exact resolve eq121 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq132 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq96 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq132 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq132
    | (have j0 := eq132 X0 X1
       grind)
    | exact resolve eq132 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq507 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq146
    | exact resolve eq146 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq628 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq663 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq628
    | (have j0 := eq628 X0 X1
       grind)
    | exact resolve eq628 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq4191 : (σ (M.op x y)) ≠ (σ x) ∨ (k x (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq129 x (σ y)
       grind)
    | exact superpose eq129 eq16
    | (have j1 := eq129 x (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq129 (M.op x y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4193 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq129 X0 X1
       grind)
    | exact superpose eq129 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq129 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq129 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq129 X0 (M.op (σ X0) X1)
       grind)
    | exact resolve eq13 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq4212 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4193 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4193
  have eq4219 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4212 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq4212
    | (have j0 := eq4212 X0 X1
       grind)
    | exact resolve eq4212 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4212
  have eq4220 : (σ (M.op x y)) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4191
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4191
    | exact resolve eq4191 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4191
  have eq4224 : ∀ X0 X1 : G, (σ X0) = X1 ∨ (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4219 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq4219
    | (have j0 := eq4219 X0 X1
       grind)
    | exact resolve eq4219 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4219
  have eq4225 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4224
  have eq4681 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4225 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4225
    | exact resolve eq4225 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4728 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq70 (σ X1) X0
       have i₂ := eq4225 X1 (σ X0)
       grind)
    | exact superpose eq4225 eq70
    | (have j1 := eq4225 X0 (σ X1)
       grind)
    | exact resolve eq70 eq4225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq4225
  have eq4790 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4728 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4728
    | (have j0 := eq4728 X0 X1
       grind)
    | exact resolve eq4728 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4728
  have eq4799 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4681 X0 X1
       have i₂ := eq99 X1 X0
       grind)
    | exact superpose eq99 eq4681
    | (have j0 := eq4681 X0 X1
       grind)
    | exact resolve eq4681 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq4681
  have eq4822 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4790 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4790
    | (have j0 := eq4790 X0 X1
       grind)
    | exact resolve eq4790 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4790
  have eq4829 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4822 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4822
    | (have j0 := eq4822 X0 X1
       grind)
    | exact resolve eq4822 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4822
  have eq4902 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq4799 X0 X1
       grind)
    | exact superpose eq4799 eq11
    | (have j1 := eq4799 X0 X1
       grind)
    | exact resolve eq11 eq4799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4799
  have eq5010 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4902 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4902
    | (have j0 := eq4902 X0 X1
       grind)
    | exact resolve eq4902 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4902
  have eq5080 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq5010 (τ X0) X1
       grind)
    | exact superpose eq5010 eq18
    | (have j1 := eq5010 (τ X0) X1
       grind)
    | exact resolve eq18 eq5010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5010
  have eq5980 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4829 X1 X0
       grind)
    | exact superpose eq4829 eq11
    | (have j1 := eq4829 X1 X0
       grind)
    | exact resolve eq11 eq4829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4829
  have eq6902 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5980 x y
       grind)
    | exact superpose eq5980 eq16
    | (have j1 := eq5980 x y
       grind)
    | exact resolve eq16 eq5980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5980
  have eq7019 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6902
       have i₂ := eq507 y x
       grind)
    | exact superpose eq507 eq6902
    | (have j1 := eq507 y (M.op x y)
       grind)
    | (have r₁ := eq6902
       have r₂ := eq507 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6902
       have r₂ := eq507 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6902 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507 eq6902
  have eq7024 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq7019
  have eq7052 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7024
       grind)
    | exact superpose eq7024 eq16
    | exact resolve eq16 eq7024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7024
  have eq7053 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7052
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq7052
    | exact resolve eq7052 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7052
  have eq7054 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7053
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq7053
    | exact resolve eq7053 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7053
  have eq7055 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7054
  have eq7295 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq25 x y
       have i₂ := eq7055
       grind)
    | exact superpose eq7055 eq25
    | exact resolve eq25 eq7055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7305 : x ≠ y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  have eq7472 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7295
       have i₂ := eq7055
       grind)
    | exact superpose eq7055 eq7295
    | exact resolve eq7295 eq7055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7055 eq7295
  have eq7491 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7472
  have eq7495 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7491
       have r₂ := eq7305
       grind)
    | exact resolve eq7491 eq7305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7305 eq7491
  have eq8514 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5080 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5080
    | exact resolve eq5080 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5080
  have eq8638 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8514 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8514
    | (have j0 := eq8514 X0 X1
       grind)
    | exact resolve eq8514 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8514
  have eq38257 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4220
       have i₂ := eq7495
       grind)
    | exact superpose eq7495 eq4220
    | exact resolve eq4220 eq7495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4220 eq7495
  have eq38263 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq38257
  have eq38264 : (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq38263
  have eq38272 : y = (τ (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq38264
       grind)
    | exact superpose eq38264 eq10
    | exact resolve eq10 eq38264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38264
  have eq38379 : x = y ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38272
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq38272
    | exact resolve eq38272 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38272
  have eq38674 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38379
       grind)
    | exact superpose eq38379 eq16
    | exact resolve eq16 eq38379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38379
  have eq38675 : (σ x) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38674
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq38674
    | exact resolve eq38674 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38674
  have eq38676 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38675
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq38675
    | exact resolve eq38675 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38675
  have eq38677 : (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq38676
  have eq38705 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq38677
       grind)
    | exact superpose eq38677 eq11
    | exact resolve eq11 eq38677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38677
  have eq39124 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38705
       grind)
    | exact superpose eq38705 eq16
    | exact resolve eq16 eq38705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39154 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) := by
    first
    | (have i₁ := eq25 (σ x) (σ y)
       have i₂ := eq38705
       grind)
    | exact superpose eq38705 eq25
    | exact resolve eq25 eq38705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq39268 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq39124
       have i₂ := eq8638 x y
       grind)
    | exact superpose eq8638 eq39124
    | (have j1 := eq8638 x y
       grind)
    | (have r₁ := eq39124
       have r₂ := eq8638 x y
       grind)
    | (have r₁ := eq39124
       have r₂ := eq8638 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq39124
       have r₂ := eq8638 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq39124 eq8638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8638
  have eq39269 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39124
       have i₂ := eq663 y x
       grind)
    | exact superpose eq663 eq39124
    | (have j1 := eq663 x y
       grind)
    | (have r₁ := eq39124
       have r₂ := eq663 y x
       grind)
    | (have r₁ := eq39124
       have r₂ := eq663 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq39124
       have r₂ := eq663 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq39124 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq39270 : x = y ∨ x = (M.op x y) := by grind
  clear eq39269
  have eq39271 : x = y ∨ y = (k x y) := by grind
  clear eq39268
  have eq39553 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39124
       have i₂ := eq39270
       grind)
    | exact superpose eq39270 eq39124
    | exact resolve eq39124 eq39270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39270
  have eq39554 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39553
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq39553
    | exact resolve eq39553 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39553
  have eq39558 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39554
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq39554
    | exact resolve eq39554 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39554
  have eq39559 : x = (M.op x y) := by grind
  clear eq39558
  have eq39945 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39124
       have i₂ := eq39271
       grind)
    | exact superpose eq39271 eq39124
    | exact resolve eq39124 eq39271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39271
  have eq39949 : (σ x) ≠ (σ (M.op x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39945
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq39945
    | exact resolve eq39945 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq39945
  have eq39953 : (σ x) ≠ (σ x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39949
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq39949
    | exact resolve eq39949 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq39949
  have eq39954 : y = (k x y) := by grind
  clear eq39953
  have eq40413 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq39124
       have i₂ := eq39954
       grind)
    | exact superpose eq39954 eq39124
    | exact resolve eq39124 eq39954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39124
  have eq40453 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq40413
       have i₂ := eq39559
       grind)
    | exact superpose eq39559 eq40413
    | exact resolve eq40413 eq39559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39559 eq40413
  have eq41246 : (σ x) = (M.op (σ x) (σ (k x (k x y)))) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (k x y))) := by
    first
    | (have i₁ := eq39154
       have i₂ := eq96 x (k x y)
       grind)
    | exact superpose eq96 eq39154
    | (have j1 := eq96 x (k x y)
       grind)
    | exact resolve eq39154 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq39154
  have eq41310 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (k x y))) := by
    first
    | (have i₁ := eq41246
       have i₂ := eq39954
       grind)
    | exact superpose eq39954 eq41246
    | exact resolve eq41246 eq39954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41246
  have eq41311 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq41310
  have eq41327 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq41311
       have i₂ := eq39954
       grind)
    | exact superpose eq39954 eq41311
    | exact resolve eq41311 eq39954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41311
  have eq41339 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq41327
       have i₂ := eq38705
       grind)
    | exact superpose eq38705 eq41327
    | exact resolve eq41327 eq38705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38705 eq41327
  have eq41340 : (σ x) = (σ (k x y)) := by grind
  clear eq41339
  have eq41348 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq41340
       have i₂ := eq39954
       grind)
    | exact superpose eq39954 eq41340
    | exact resolve eq41340 eq39954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39954 eq41340
  have eq41354 : False := by grind
  exact eq41354

/-- `Equation418`: `x = x ◇ (x ◇ (y ◇ (x ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_y_pxy_Equation418 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law418 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law418.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X0 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 (M.op X0 x)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq22 (M.op X0 X1)
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq34
    | exact resolve eq34 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq67 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq76 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq87 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq22 (σ X1)
       grind)
    | exact superpose eq22 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq94 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq22 (τ X1)
       grind)
    | exact superpose eq22 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq96 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq67
    | exact resolve eq67 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq76
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq76 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq126 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq118 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq118
    | (have j0 := eq118 X0 X1
       grind)
    | exact resolve eq118 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq129 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq93 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq129 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq129
    | (have j0 := eq129 X0 X1
       grind)
    | exact resolve eq129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq502 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq143
    | exact resolve eq143 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq623 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq658 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq623 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq623
    | (have j0 := eq623 X0 X1
       grind)
    | exact resolve eq623 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq4175 : (σ (M.op x y)) ≠ (σ x) ∨ (k x (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq126 x (σ y)
       grind)
    | exact superpose eq126 eq16
    | (have j1 := eq126 x (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq126 (M.op x y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4177 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq126 X0 X1
       grind)
    | exact superpose eq126 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq126 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq126 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq126 X0 (M.op (σ X0) X1)
       grind)
    | exact resolve eq13 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq4196 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4177 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4177
  have eq4203 : ∀ X0 X1 : G, (σ X0) = X1 ∨ (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4196 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq4196
    | (have j0 := eq4196 X0 X1
       grind)
    | exact resolve eq4196 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4196
  have eq4204 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4203 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4203
  have eq4205 : (σ (M.op x y)) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4175
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4175
    | exact resolve eq4175 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4175
  have eq4662 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4204 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4204
    | exact resolve eq4204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4709 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X1) X0
       have i₂ := eq4204 X1 (σ X0)
       grind)
    | exact superpose eq4204 eq67
    | (have j1 := eq4204 X0 (σ X1)
       grind)
    | exact resolve eq67 eq4204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq4204
  have eq4771 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4709 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4709
    | (have j0 := eq4709 X0 X1
       grind)
    | exact resolve eq4709 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4709
  have eq4780 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4662 X0 X1
       have i₂ := eq96 X1 X0
       grind)
    | exact superpose eq96 eq4662
    | (have j0 := eq4662 X0 X1
       grind)
    | exact resolve eq4662 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq4662
  have eq4803 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4771 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4771
    | (have j0 := eq4771 X0 X1
       grind)
    | exact resolve eq4771 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4771
  have eq4810 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4803 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4803
    | (have j0 := eq4803 X0 X1
       grind)
    | exact resolve eq4803 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4803
  have eq4882 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq4780 X0 X1
       grind)
    | exact superpose eq4780 eq11
    | (have j1 := eq4780 X0 X1
       grind)
    | exact resolve eq11 eq4780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4780
  have eq4990 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4882 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq4882
    | (have j0 := eq4882 X0 X1
       grind)
    | exact resolve eq4882 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4882
  have eq5060 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq4990 (τ X0) X1
       grind)
    | exact superpose eq4990 eq18
    | (have j1 := eq4990 (τ X0) X1
       grind)
    | exact resolve eq18 eq4990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4990
  have eq5955 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4810 X1 X0
       grind)
    | exact superpose eq4810 eq11
    | (have j1 := eq4810 X1 X0
       grind)
    | exact resolve eq11 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4810
  have eq6874 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5955 x y
       grind)
    | exact superpose eq5955 eq16
    | (have j1 := eq5955 x y
       grind)
    | exact resolve eq16 eq5955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5955
  have eq6989 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6874
       have i₂ := eq502 y x
       grind)
    | exact superpose eq502 eq6874
    | (have j1 := eq502 y (M.op x y)
       grind)
    | (have r₁ := eq6874
       have r₂ := eq502 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6874
       have r₂ := eq502 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6874 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq6874
  have eq6994 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6989
  have eq7022 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6994
       grind)
    | exact superpose eq6994 eq16
    | exact resolve eq16 eq6994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6994
  have eq7023 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7022
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq7022
    | exact resolve eq7022 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7022
  have eq7024 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7023
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq7023
    | exact resolve eq7023 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7023
  have eq7025 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7024
  have eq7264 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq25 x y
       have i₂ := eq7025
       grind)
    | exact superpose eq7025 eq25
    | exact resolve eq25 eq7025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7274 : x ≠ y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  have eq7438 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7264
       have i₂ := eq7025
       grind)
    | exact superpose eq7025 eq7264
    | exact resolve eq7264 eq7025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7025 eq7264
  have eq7457 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq7438
  have eq7460 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7457
       have r₂ := eq7274
       grind)
    | exact resolve eq7457 eq7274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7274 eq7457
  have eq8466 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5060 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5060
    | exact resolve eq5060 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5060
  have eq8590 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8466 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8466
    | (have j0 := eq8466 X0 X1
       grind)
    | exact resolve eq8466 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8466
  have eq38165 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4205
       have i₂ := eq7460
       grind)
    | exact superpose eq7460 eq4205
    | exact resolve eq4205 eq7460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4205 eq7460
  have eq38171 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by grind
  clear eq38165
  have eq38172 : (σ x) = (σ y) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq38171
  have eq38180 : y = (τ (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq38172
       grind)
    | exact superpose eq38172 eq10
    | exact resolve eq10 eq38172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38172
  have eq38287 : x = y ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38180
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq38180
    | exact resolve eq38180 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38180
  have eq38581 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38287
       grind)
    | exact superpose eq38287 eq16
    | exact resolve eq16 eq38287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38287
  have eq38582 : (σ x) ≠ (σ (M.op x x)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38581
       have i₂ := eq22 (σ x)
       grind)
    | exact superpose eq22 eq38581
    | exact resolve eq38581 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38581
  have eq38583 : (σ x) ≠ (σ x) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38582
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq38582
    | exact resolve eq38582 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38582
  have eq38584 : (k x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq38583
  have eq38612 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq11 (M.op (σ x) (σ y))
       have i₂ := eq38584
       grind)
    | exact superpose eq38584 eq11
    | exact resolve eq11 eq38584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38584
  have eq39030 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38612
       grind)
    | exact superpose eq38612 eq16
    | exact resolve eq16 eq38612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39060 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (k x y)))) := by
    first
    | (have i₁ := eq25 (σ x) (σ y)
       have i₂ := eq38612
       grind)
    | exact superpose eq38612 eq25
    | exact resolve eq25 eq38612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq39173 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq39030
       have i₂ := eq8590 x y
       grind)
    | exact superpose eq8590 eq39030
    | (have j1 := eq8590 x y
       grind)
    | (have r₁ := eq39030
       have r₂ := eq8590 x y
       grind)
    | (have r₁ := eq39030
       have r₂ := eq8590 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq39030
       have r₂ := eq8590 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq39030 eq8590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8590
  have eq39174 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39030
       have i₂ := eq658 y x
       grind)
    | exact superpose eq658 eq39030
    | (have j1 := eq658 x y
       grind)
    | (have r₁ := eq39030
       have r₂ := eq658 y x
       grind)
    | (have r₁ := eq39030
       have r₂ := eq658 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq39030
       have r₂ := eq658 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq39030 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq39175 : x = y ∨ x = (M.op x y) := by grind
  clear eq39174
  have eq39176 : x = y ∨ y = (k x y) := by grind
  clear eq39173
  have eq39457 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39030
       have i₂ := eq39175
       grind)
    | exact superpose eq39175 eq39030
    | exact resolve eq39030 eq39175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39175
  have eq39458 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39457
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq39457
    | exact resolve eq39457 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39457
  have eq39462 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39458
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq39458
    | exact resolve eq39458 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39458
  have eq39463 : x = (M.op x y) := by grind
  clear eq39462
  have eq39846 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39030
       have i₂ := eq39176
       grind)
    | exact superpose eq39176 eq39030
    | exact resolve eq39030 eq39176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39176
  have eq39850 : (σ x) ≠ (σ (M.op x x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39846
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq39846
    | exact resolve eq39846 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq39846
  have eq39854 : (σ x) ≠ (σ x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq39850
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq39850
    | exact resolve eq39850 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq39850
  have eq39855 : y = (k x y) := by grind
  clear eq39854
  have eq40313 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq39030
       have i₂ := eq39855
       grind)
    | exact superpose eq39855 eq39030
    | exact resolve eq39030 eq39855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39030
  have eq40353 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq40313
       have i₂ := eq39463
       grind)
    | exact superpose eq39463 eq40313
    | exact resolve eq40313 eq39463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39463 eq40313
  have eq41145 : (σ x) = (M.op (σ x) (σ (k x (k x y)))) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (k x y))) := by
    first
    | (have i₁ := eq39060
       have i₂ := eq93 x (k x y)
       grind)
    | exact superpose eq93 eq39060
    | (have j1 := eq93 x (k x y)
       grind)
    | exact resolve eq39060 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq39060
  have eq41209 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ (k x y))) := by
    first
    | (have i₁ := eq41145
       have i₂ := eq39855
       grind)
    | exact superpose eq39855 eq41145
    | exact resolve eq41145 eq39855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41145
  have eq41210 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq41209
  have eq41226 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq41210
       have i₂ := eq39855
       grind)
    | exact superpose eq39855 eq41210
    | exact resolve eq41210 eq39855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41210
  have eq41238 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq41226
       have i₂ := eq38612
       grind)
    | exact superpose eq38612 eq41226
    | exact resolve eq41226 eq38612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38612 eq41226
  have eq41239 : (σ x) = (σ (k x y)) := by grind
  clear eq41238
  have eq41246 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq41239
       have i₂ := eq39855
       grind)
    | exact superpose eq39855 eq41239
    | exact resolve eq41239 eq39855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39855 eq41239
  have eq41252 : False := by grind
  exact eq41252
