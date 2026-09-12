import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq78 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq95 x y
       grind)
    | exact superpose eq95 eq44
    | (have j1 := eq95 x y
       grind)
    | exact resolve eq44 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq118
    | exact resolve eq118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120
    | exact resolve eq120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq121 eq95
    | (have j0 := eq95 (σ x) (σ y)
       grind)
    | exact resolve eq95 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq125
       have r₂ := eq27
       grind)
    | exact resolve eq125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq130 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq132 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq27
    | exact resolve eq27 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq404 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq78
    | (have r₁ := eq78
       have r₂ := eq130
       grind)
    | exact resolve eq78 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq130
  have eq405 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq404
  have eq409 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq405 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq405
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq405
       grind)
    | exact resolve eq13 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq412 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq409
  have eq416 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq412
    | exact resolve eq412 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq419 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq121 eq416
    | exact resolve eq416 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq416
  have eq427 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq419
  have eq430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq427
       have r₂ := eq132
       grind)
    | exact resolve eq427 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq427
  have eq431 : x = (M.op x y) := by
    first
    | (have r₁ := eq430
       have r₂ := eq27
       grind)
    | exact resolve eq430 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq432 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq431 eq20
    | exact resolve eq20 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq435 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq431 eq53
    | exact resolve eq53 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq442 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq431 eq221
    | exact resolve eq221 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq450 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq432
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq432
    | exact resolve eq432 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq499 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) (M.op x y)) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y X1
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq509 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (M.op x X0) x) X1)) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq431 eq499
    | exact resolve eq499 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq517 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq450 eq26
    | exact resolve eq26 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1015 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq509 X0 X0
       have i₂ := eq435 X0
       grind)
    | exact superpose eq435 eq509
    | exact resolve eq509 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq1039 : x = (M.op x x) := by
    first
    | (have i₁ := eq435 x
       have i₂ := eq1015 x
       grind)
    | exact superpose eq1015 eq435
    | exact resolve eq435 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq1015
  have eq1053 : y = (M.op x y) := by
    first
    | (have i₁ := eq442
       have i₂ := eq1039
       grind)
    | exact superpose eq1039 eq442
    | exact resolve eq442 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq1059 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq1039
       grind)
    | exact superpose eq1039 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq1039
       grind)
    | exact resolve eq13 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1071 : x = (k x x) := by grind
  clear eq1059
  have eq1075 : y = (M.op x y) := by
    first
    | (have i₁ := eq1053
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1053
    | exact resolve eq1053 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1053
  have eq1076 : x = y := by
    first
    | exact superpose eq431 eq1075
    | exact resolve eq1075 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq1075
  have eq1078 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1076
       grind)
    | exact superpose eq1076 eq24
    | exact resolve eq24 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1076
  have eq1100 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1078
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1078
    | exact resolve eq1078 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1108 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq450 eq1100
    | exact resolve eq1100 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1143 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1108 eq517
    | exact resolve eq517 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq1108
  have eq1171 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1071
       grind)
    | exact superpose eq1071 eq43
    | exact resolve eq43 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1071
  have eq1175 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq450 eq1171
    | exact resolve eq1171 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq1176 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1175
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1175
    | exact resolve eq1175 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1175
  have eq1177 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq450 eq1176
    | exact resolve eq1176 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq1176
  have eq1198 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1177 eq95
    | (have j0 := eq95 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq95 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq1177
  have eq1199 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1198
  have eq1246 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1143 eq1199
    | exact resolve eq1199 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143 eq1199
  have eq1247 : False := by grind
  exact eq1247

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pyy_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq630 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq801 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq630
       grind)
    | exact superpose eq630 eq40
    | exact resolve eq40 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq630
  have eq802 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq801
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq801
    | exact resolve eq801 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq804 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq802
    | exact resolve eq802 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq870 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq199
    | exact resolve eq199 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq893 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq870 X0
       grind)
    | exact superpose eq870 eq16
    | exact resolve eq16 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq937 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq893 (M.op X1 X0) X0
       have i₂ := eq16 X0 X1 X0
       grind)
    | exact superpose eq16 eq893
    | exact resolve eq893 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq893 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq893
    | exact resolve eq893 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq949 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq177 eq893
    | exact resolve eq893 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq953 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq178 eq893
    | exact resolve eq893 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq893
  have eq969 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq949 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq949
       grind)
    | exact resolve eq12 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq973 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq969
  have eq980 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq953 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq953
       grind)
    | exact resolve eq12 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq984 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq980
  have eq1371 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq973 eq35
    | exact resolve eq35 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq973
  have eq1374 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq20 eq1371
    | exact resolve eq1371 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq1667 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq804 eq631
    | exact resolve eq631 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1674 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1667
       have r₂ := eq27
       grind)
    | exact resolve eq1667 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667
  have eq1682 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1674 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1674
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1674
       grind)
    | exact resolve eq13 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1690 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1674 eq945
    | exact resolve eq945 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq1691 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq1682
  have eq1696 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq804 eq1691
    | exact resolve eq1691 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1700 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1690 eq1696
    | exact resolve eq1696 eq1690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1690 eq1696
  have eq1707 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq1700
       grind)
    | exact superpose eq1700 eq16
    | exact resolve eq16 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1714 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq945 y x
       have i₂ := eq1700
       grind)
    | exact superpose eq1700 eq945
    | exact resolve eq945 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700
  have eq1719 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1707 X0
       have i₂ := eq581 X0
       grind)
    | exact superpose eq581 eq1707
    | exact resolve eq1707 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707
  have eq2152 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1719 y
       have i₂ := eq1714
       grind)
    | exact superpose eq1714 eq1719
    | exact resolve eq1719 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714
  have eq2175 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2152
  have eq2188 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq2175
       grind)
    | exact superpose eq2175 eq16
    | exact resolve eq16 eq2175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq2203 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1719 eq2188
    | exact resolve eq2188 eq1719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719 eq2188
  have eq2283 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2203 y
       grind)
    | exact superpose eq2203 eq18
    | (have j1 := eq2203 y
       grind)
    | exact resolve eq18 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203
  have eq2305 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2283
  have eq2334 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2305 eq984
    | exact resolve eq984 eq2305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984 eq2305
  have eq2749 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2334 eq804
    | exact resolve eq804 eq2334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334
  have eq2762 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2749
  have eq3115 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2762 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2762
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2762
       grind)
    | exact resolve eq13 eq2762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3127 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2762 eq945
    | exact resolve eq945 eq2762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2762
  have eq3130 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3115
  have eq3139 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq804 eq3130
    | exact resolve eq3130 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804 eq3130
  have eq3145 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3127 eq3139
    | exact resolve eq3139 eq3127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3127 eq3139
  have eq3146 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3145
  have eq3160 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq3146
       grind)
    | exact superpose eq3146 eq16
    | exact resolve eq16 eq3146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3171 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq945 y x
       have i₂ := eq3146
       grind)
    | exact superpose eq3146 eq945
    | exact resolve eq945 eq3146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3146
  have eq3184 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq3160 X0
       have i₂ := eq581 X0
       grind)
    | exact superpose eq581 eq3160
    | exact resolve eq3160 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581 eq3160
  have eq3372 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3184 y
       have i₂ := eq3171
       grind)
    | exact superpose eq3171 eq3184
    | exact resolve eq3184 eq3171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3171
  have eq3403 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3372
  have eq3424 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq3403
       grind)
    | exact superpose eq3403 eq16
    | exact resolve eq16 eq3403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3403
  have eq3450 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq3184 eq3424
    | exact resolve eq3424 eq3184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3184 eq3424
  have eq3602 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3450 y
       grind)
    | exact superpose eq3450 eq18
    | (have j1 := eq3450 y
       grind)
    | exact resolve eq18 eq3450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3450
  have eq3628 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq3602
  have eq3641 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3628 eq28
    | exact resolve eq28 eq3628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3628
  have eq3661 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq3641
    | exact resolve eq3641 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3641
  have eq3662 : y = (M.op x y) := by grind
  clear eq3661
  have eq3673 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3662
       grind)
    | exact superpose eq3662 eq24
    | exact resolve eq24 eq3662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3662
  have eq3700 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3673 eq20
    | exact resolve eq20 eq3673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3703 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq3673 eq15
    | exact resolve eq15 eq3673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3734 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq3700 eq1374
    | exact resolve eq1374 eq3700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq4016 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq3734 eq631
    | exact resolve eq631 eq3734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq3734
  have eq4026 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq4016
  have eq5359 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq4026 eq16
    | exact resolve eq16 eq4026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5374 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq4026 eq945
    | exact resolve eq945 eq4026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq5388 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq726 eq5359
    | exact resolve eq5359 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq5359
  have eq8741 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq5374 eq5388
    | exact resolve eq5388 eq5374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5374 eq5388
  have eq8779 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq8741
  have eq8793 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq8779 eq4026
    | exact resolve eq4026 eq8779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4026 eq8779
  have eq8832 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8793
  have eq8886 : x = (M.op (M.op x (M.op x y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq8832 eq937
    | exact resolve eq937 eq8832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq8895 : x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq949 eq8886
    | exact resolve eq8886 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8886
  have eq8908 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq8832 eq8895
    | exact resolve eq8895 eq8832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8832 eq8895
  have eq8916 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq8908 eq27
    | exact resolve eq27 eq8908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8908
  have eq8944 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8916
       have r₂ := eq3700
       grind)
    | exact resolve eq8916 eq3700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8916
  have eq9003 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8944 eq3703
    | exact resolve eq3703 eq8944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3703 eq8944
  have eq9039 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq9003
    | exact resolve eq9003 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq9003
  have eq9040 : x = (M.op x y) := by grind
  clear eq9039
  have eq9065 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq9040
       grind)
    | exact superpose eq9040 eq22
    | exact resolve eq22 eq9040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq9076 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq949
       have i₂ := eq9040
       grind)
    | exact superpose eq9040 eq949
    | exact resolve eq949 eq9040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949 eq9040
  have eq9127 : (σ x) = (σ y) := by
    first
    | exact superpose eq9065 eq3673
    | exact resolve eq3673 eq9065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3673
  have eq9128 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9065 eq20
    | exact resolve eq20 eq9065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9065
  have eq9214 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9127 eq26
    | exact resolve eq26 eq9127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq9412 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq9076 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq9076
       grind)
    | exact resolve eq13 eq9076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9076
  have eq9435 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq9412
  have eq9457 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq9435 eq37
    | exact resolve eq37 eq9435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq9435
  have eq9476 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq9457
    | exact resolve eq9457 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9457
  have eq9482 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq3700 eq9476
    | exact resolve eq9476 eq3700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3700 eq9476
  have eq9488 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq9127 eq9482
    | exact resolve eq9482 eq9127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9127 eq9482
  have eq9507 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9214 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq9214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9214
  have eq9532 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9507
  have eq9536 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9488 eq9532
    | exact resolve eq9532 eq9488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9488 eq9532
  have eq9537 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9536
  have eq9542 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq9537 eq27
    | exact resolve eq27 eq9537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq9537
  have eq9597 : False := by grind
  exact eq9597

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then Y else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_y_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
  have eq56 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
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
  have eq70 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq94
    | exact resolve eq94 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq142 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq125
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq125
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq149 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq142
  have eq401 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq401 X0
       grind)
    | exact superpose eq401 eq14
    | exact resolve eq14 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) X5)) X1) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq59 X1 (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X0 X5
       have i₂ := eq62 X3 X2 X4 X0
       grind)
    | exact superpose eq62 eq59
    | exact resolve eq59 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq62
  have eq674 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq401 (σ X0)
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq401
    | (have j1 := eq79 X0 X0
       grind)
    | exact resolve eq401 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq79 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq678 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq677 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq681 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq674 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq1029 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq408 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq408
    | exact resolve eq408 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq11201 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) (M.op X0 X4)) (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq480 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X1 X0 X2 X4
       have i₂ := eq14 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq14 eq480
    | exact resolve eq480 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq11238 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op X0 X3) (M.op X0 X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq11201 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq11201
    | exact resolve eq11201 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11201
  have eq28882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq28892 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq28882
    | exact resolve eq28882 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28882
  have eq28903 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq28892
       have r₂ := eq28
       grind)
    | exact resolve eq28892 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28892
  have eq28905 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28903 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq28903
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq28903
       grind)
    | exact resolve eq13 eq28903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28903
  have eq28957 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq28905
  have eq29143 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28957 eq56
    | exact resolve eq56 eq28957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28957
  have eq29171 : y = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq29143
    | exact resolve eq29143 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29143
  have eq29174 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq29171
       have r₂ := eq13 x y
       grind)
    | exact resolve eq29171 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29171
  have eq29181 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29174 eq70
    | exact resolve eq70 eq29174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29174
  have eq29430 : (τ (σ y)) = (k x y) ∨ y = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29181 eq56
    | exact resolve eq56 eq29181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq29181
  have eq29457 : y = (k x y) ∨ y = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq29430
    | exact resolve eq29430 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq29430
  have eq29458 : y = (k x y) ∨ x = (M.op y y) := by grind
  clear eq29457
  have eq29525 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq29458
       grind)
    | exact superpose eq29458 eq45
    | exact resolve eq45 eq29458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq29534 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq29458
       grind)
    | exact superpose eq29458 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq29458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29458
  have eq29544 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq29534
  have eq29555 : y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29544
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29544
    | exact resolve eq29544 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29544
  have eq29564 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq29525
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq29525
    | exact resolve eq29525 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29525
  have eq29715 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq29555
       grind)
    | exact superpose eq29555 eq14
    | exact resolve eq14 eq29555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29761 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1029 y x
       have i₂ := eq29555
       grind)
    | exact superpose eq29555 eq1029
    | exact resolve eq1029 eq29555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29791 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq29715 X0
       have i₂ := eq1029 y X0
       grind)
    | exact superpose eq1029 eq29715
    | exact resolve eq29715 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29715
  have eq30044 : x ≠ y ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq29761
  have eq33236 : x = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29791 x
       have i₂ := eq29555
       grind)
    | exact superpose eq29555 eq29791
    | exact resolve eq29791 eq29555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29791
  have eq33325 : x = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq33236
  have eq33406 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1029 y y
       have i₂ := eq33325
       grind)
    | exact superpose eq33325 eq1029
    | exact resolve eq1029 eq33325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33325
  have eq33410 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq33406
  have eq33420 : x = y ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq29555
       have i₂ := eq33410
       grind)
    | exact superpose eq33410 eq29555
    | exact resolve eq29555 eq33410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29555 eq33410
  have eq33474 : x = y ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq33420
  have eq33477 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq33474
       have r₂ := eq30044
       grind)
    | exact resolve eq33474 eq30044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30044 eq33474
  have eq33487 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq401 y
       have i₂ := eq33477
       grind)
    | exact superpose eq33477 eq401
    | exact resolve eq401 eq33477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33477
  have eq33548 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33487
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq33487
    | exact resolve eq33487 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq33487
  have eq33549 : y = (M.op x y) := by grind
  clear eq33548
  have eq33551 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq33549 eq21
    | exact resolve eq21 eq33549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq33580 : (σ (M.op y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq33549 eq149
    | exact resolve eq149 eq33549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq33720 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq33551
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33551
    | exact resolve eq33551 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33551
  have eq33721 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq33720 eq27
    | exact resolve eq27 eq33720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq33824 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq33720 eq29564
    | exact resolve eq29564 eq33720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29564
  have eq34525 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq33824 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq33824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33824
  have eq34535 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq33721 eq34525
    | exact resolve eq34525 eq33721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34525
  have eq34546 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq34535
       have r₂ := eq28
       grind)
    | exact resolve eq34535 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34535
  have eq40136 : (σ y) = (M.op (σ (k y y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq681 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq681
    | (have j0 := eq681 y
       grind)
    | exact resolve eq681 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq40213 : (σ (M.op x y)) = (M.op (σ (k y y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq33720 eq40136
    | exact resolve eq40136 eq33720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40136
  have eq40299 : (σ (M.op x y)) = (M.op (k (σ y) (σ y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq40213
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq40213
    | exact resolve eq40213 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq40213
  have eq40363 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq33720 eq40299
    | exact resolve eq40299 eq33720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40299
  have eq40398 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq33720 eq40363
    | exact resolve eq40363 eq33720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40363
  have eq41593 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq34546 eq401
    | exact resolve eq401 eq34546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401 eq34546
  have eq41661 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq33721 eq41593
    | exact resolve eq41593 eq33721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41593
  have eq41664 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq41661
       have r₂ := eq28
       grind)
    | exact resolve eq41661 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41661
  have eq41669 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq41664 eq14
    | exact resolve eq14 eq41664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41724 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq41664 eq11238
    | exact resolve eq11238 eq41664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11238
  have eq41728 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq41724 x
       have i₂ := eq1029 sF1 x
       grind)
    | exact superpose eq1029 eq41724
    | exact resolve eq41724 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41724
  have eq41757 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq41669 x
       have i₂ := eq1029 sF1 x
       grind)
    | exact superpose eq1029 eq41669
    | exact resolve eq41669 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029 eq41669
  have eq43893 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq41664 eq41757
    | exact resolve eq41757 eq41664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41664 eq41757
  have eq43997 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq43893
  have eq44029 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq43997 eq41728
    | exact resolve eq41728 eq43997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41728 eq43997
  have eq44090 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by grind
  clear eq44029
  have eq44095 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq33721 eq44090
    | exact resolve eq44090 eq33721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44090
  have eq44097 : x = (M.op y y) := by
    first
    | (have r₁ := eq44095
       have r₂ := eq28
       grind)
    | exact resolve eq44095 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44095
  have eq44103 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq33580
       have i₂ := eq44097
       grind)
    | exact superpose eq44097 eq33580
    | exact resolve eq33580 eq44097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33580
  have eq44115 : x ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq44097
       grind)
    | exact superpose eq44097 eq13
    | (have j0 := eq13 y y
       grind)
    | exact resolve eq13 eq44097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44097
  have eq44176 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq44103
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44103
    | exact resolve eq44103 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44103
  have eq45577 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq44176 eq148
    | exact resolve eq148 eq44176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45590 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq44176 eq40398
    | exact resolve eq40398 eq44176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40398 eq44176
  have eq45618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq33721 eq45590
    | exact resolve eq45590 eq33721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45590
  have eq45625 : (τ (σ x)) = (k y y) ∨ x = y := by
    first
    | exact superpose eq33549 eq45577
    | exact resolve eq45577 eq33549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45577
  have eq45628 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq45618
       have r₂ := eq28
       grind)
    | exact resolve eq45618 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45618
  have eq45635 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq29 eq45625
    | exact resolve eq45625 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq45625
  have eq45646 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq45628 eq70
    | exact resolve eq70 eq45628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq45628
  have eq45891 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq45646 eq148
    | exact resolve eq148 eq45646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq45646
  have eq45950 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq33549 eq45891
    | exact resolve eq45891 eq33549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45891
  have eq45960 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq31 eq45950
    | exact resolve eq45950 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq45950
  have eq45968 : y = (k y y) ∨ x = y := by
    first
    | exact superpose eq33549 eq45960
    | exact resolve eq45960 eq33549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33549 eq45960
  have eq45972 : y = (k y y) := by
    first
    | (have r₁ := eq45968
       have r₂ := eq44115
       grind)
    | exact resolve eq45968 eq44115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44115 eq45968
  have eq45988 : x = y ∨ x = y := by
    first
    | (have i₁ := eq45635
       have i₂ := eq45972
       grind)
    | exact superpose eq45972 eq45635
    | exact resolve eq45635 eq45972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45635
  have eq45993 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq678 y
       have i₂ := eq45972
       grind)
    | exact superpose eq45972 eq678
    | (have j0 := eq678 y
       grind)
    | exact resolve eq678 eq45972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq45972
  have eq46012 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq45993
  have eq46015 : x = y := by grind
  clear eq45988
  have eq46029 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq46012
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq46012
    | exact resolve eq46012 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46012
  have eq46053 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq33720 eq46029
    | exact resolve eq46029 eq33720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46029
  have eq46774 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq46015
       grind)
    | exact superpose eq46015 eq25
    | exact resolve eq25 eq46015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq46015
  have eq47025 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq33720 eq46774
    | exact resolve eq46774 eq33720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33720 eq46774
  have eq47113 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq47025
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq47025
    | exact resolve eq47025 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq47025
  have eq47272 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq47113 eq33721
    | exact resolve eq33721 eq47113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33721 eq47113
  have eq49265 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46053 eq47272
    | exact resolve eq47272 eq46053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46053 eq47272
  have eq49266 : False := by grind
  exact eq49266

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pyx_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq22
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
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
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74
    | exact resolve eq74 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq81
    | exact resolve eq81 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq101 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq101
  have eq126 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq143 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq126
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq126
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq126 eq16
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq143
  have eq186 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq206 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq208 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq416 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq424 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq416 X0
       grind)
    | exact superpose eq416 eq14
    | exact resolve eq14 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq485 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq208 eq55
    | exact resolve eq55 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq208
  have eq893 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq424 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq424
    | exact resolve eq424 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6259 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq186 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq186
    | (have j0 := eq186 y
       grind)
    | exact resolve eq186 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq6280 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6259
  have eq6283 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6280
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq6280
    | exact resolve eq6280 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6280
  have eq6306 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6283
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6283 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6283
  have eq6320 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6306 eq106
    | exact resolve eq106 eq6306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq6443 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq206
    | (have j0 := eq206 (M.op x y)
       grind)
    | exact resolve eq206 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq6463 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6443
  have eq6465 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq126 eq6463
    | exact resolve eq6463 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6463
  have eq6495 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6465
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6465 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6465
  have eq6518 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq6495 eq149
    | exact resolve eq149 eq6495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq10158 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6306 eq107
    | exact resolve eq107 eq6306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq10914 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6495 eq150
    | exact resolve eq150 eq6495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq21707 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq10158
       grind)
    | exact superpose eq10158 eq16
    | exact resolve eq16 eq10158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10158
  have eq21763 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6320 eq21707
    | exact resolve eq21707 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21707
  have eq21769 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq21763
       have r₂ := eq13 y y
       grind)
    | exact resolve eq21763 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21763
  have eq21979 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq90
       have i₂ := eq21769
       grind)
    | exact superpose eq21769 eq90
    | exact resolve eq90 eq21769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq22011 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq6306 eq21979
    | exact resolve eq21979 eq6306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6306 eq21979
  have eq28023 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq10914 eq16
    | exact resolve eq16 eq10914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10914
  have eq28091 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6518 eq28023
    | exact resolve eq28023 eq6518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6518 eq28023
  have eq28097 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq28091
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq28091 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28091
  have eq28099 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq28097 eq126
    | exact resolve eq126 eq28097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq28097
  have eq28140 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq6495 eq28099
    | exact resolve eq28099 eq6495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6495 eq28099
  have eq34441 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq82 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq34451 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq34441
    | exact resolve eq34441 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34441
  have eq34462 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq34451
       have r₂ := eq27
       grind)
    | exact resolve eq34451 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34451
  have eq34466 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq34462 eq6320
    | exact resolve eq6320 eq34462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34462
  have eq34572 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq34466
       have i₂ := eq21769
       grind)
    | exact superpose eq21769 eq34466
    | exact resolve eq34466 eq21769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34466
  have eq34588 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq34572
    | exact resolve eq34572 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34572
  have eq34589 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq34588
  have eq34639 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq34589 eq893
    | exact resolve eq893 eq34589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34589
  have eq34678 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq34639 eq6320
    | exact resolve eq6320 eq34639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6320 eq34639
  have eq34784 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq34678
       have i₂ := eq21769
       grind)
    | exact superpose eq21769 eq34678
    | exact resolve eq34678 eq21769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21769 eq34678
  have eq34800 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq34784
    | exact resolve eq34784 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq34784
  have eq34801 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq34800
  have eq34875 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq424 y X0
       have i₂ := eq34801
       grind)
    | exact superpose eq34801 eq424
    | exact resolve eq424 eq34801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34879 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq34801
       grind)
    | exact superpose eq34801 eq14
    | exact resolve eq14 eq34801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34801
  have eq34955 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq34879 X0
       have i₂ := eq893 y X0
       grind)
    | exact superpose eq893 eq34879
    | exact resolve eq34879 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34879
  have eq35441 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq34875 X0
       have i₂ := eq34955 X0
       grind)
    | exact superpose eq34955 eq34875
    | exact resolve eq34875 eq34955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34875 eq34955
  have eq35523 : ∀ X0 : G, y = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq35441 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35441
  have eq35700 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq893 y x
       have i₂ := eq35523 X0
       grind)
    | exact superpose eq35523 eq893
    | (have j1 := eq35523 y
       grind)
    | exact resolve eq893 eq35523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35523
  have eq35975 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq35700 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35700
  have eq35976 : y = (M.op y y) := by grind
  clear eq35975
  have eq36033 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq22011
       have i₂ := eq35976
       grind)
    | exact superpose eq35976 eq22011
    | exact resolve eq22011 eq35976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36042 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq424 y X0
       have i₂ := eq35976
       grind)
    | exact superpose eq35976 eq424
    | exact resolve eq424 eq35976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq36046 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq35976
       grind)
    | exact superpose eq35976 eq14
    | exact resolve eq14 eq35976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35976
  have eq36122 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq36046 X0
       have i₂ := eq893 y X0
       grind)
    | exact superpose eq893 eq36046
    | exact resolve eq36046 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq36046
  have eq36129 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq36033
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36033
    | exact resolve eq36033 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36033
  have eq36613 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq36042 X0
       have i₂ := eq36122 X0
       grind)
    | exact superpose eq36122 eq36042
    | exact resolve eq36042 eq36122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36042
  have eq36680 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq36122 X0
       have i₂ := eq36613 X0
       grind)
    | exact superpose eq36613 eq36122
    | exact resolve eq36122 eq36613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36122
  have eq36929 : y = (M.op x y) := by
    first
    | (have i₁ := eq36680 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq36680
    | (have j0 := eq36680 x
       grind)
    | exact resolve eq36680 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq37577 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq36929 eq20
    | exact resolve eq20 eq36929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq37693 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y y)) := by
    first
    | exact superpose eq36929 eq28140
    | exact resolve eq28140 eq36929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28140 eq36929
  have eq37701 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq37693
       have i₂ := eq22011
       grind)
    | exact superpose eq22011 eq37693
    | exact resolve eq37693 eq22011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22011 eq37693
  have eq37791 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq37577
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37577
    | exact resolve eq37577 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37577
  have eq37794 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq36129 eq37701
    | exact resolve eq37701 eq36129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36129 eq37701
  have eq38006 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq37791 eq26
    | exact resolve eq26 eq37791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq38457 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq37791 eq37794
    | exact resolve eq37794 eq37791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37791 eq37794
  have eq38462 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq485 X0 X1
       have i₂ := eq36680 (M.op (M.op sF0 sF0) X0)
       grind)
    | exact superpose eq36680 eq485
    | exact resolve eq485 eq36680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq36680
  have eq38463 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38462 X0 X1
       have i₂ := eq36613 X1
       grind)
    | exact superpose eq36613 eq38462
    | exact resolve eq38462 eq36613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36613 eq38462
  have eq38905 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq38457 eq14
    | exact resolve eq14 eq38457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38457
  have eq38988 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq38905 X0
       have i₂ := eq38463 X0 sF1
       grind)
    | exact superpose eq38463 eq38905
    | exact resolve eq38905 eq38463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38905
  have eq41672 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq38988 eq38463
    | exact resolve eq38463 eq38988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38463 eq38988
  have eq42161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41672 eq38006
    | exact resolve eq38006 eq41672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38006 eq41672
  have eq42205 : False := by grind
  exact eq42205

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq43 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq43 (σ X0)
       grind)
    | exact superpose eq43 eq15
    | exact resolve eq15 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq19
    | exact resolve eq19 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq57
    | exact resolve eq57 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq63
    | exact resolve eq63 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq79 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq10
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq153 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq183 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq116 (τ X0)
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq116
    | exact resolve eq116 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq116
  have eq201 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq9
    | exact resolve eq9 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq348 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op (σ X0) (σ X0))) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq201 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq201
    | exact resolve eq201 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq360 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (σ (M.op X0 X0))) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq348 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq348
    | exact resolve eq348 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq362 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq360 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq360
    | exact resolve eq360 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq401 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq362 (σ X0) X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq362
    | exact resolve eq362 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq362 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq362
    | exact resolve eq362 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq407 X0 X1
       grind)
    | exact superpose eq407 eq9
    | exact resolve eq9 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq153
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq153
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq153
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq153
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq153 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq662 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq661
  have eq800 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq362 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq401 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq401 eq362
    | exact resolve eq362 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq905 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq800 X0
       grind)
    | exact superpose eq800 eq12
    | exact resolve eq12 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq914 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq905 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq905
    | (have j0 := eq905 X0
       grind)
    | exact resolve eq905 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq8413 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq662
       grind)
    | exact superpose eq662 eq16
    | exact resolve eq16 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq8414 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq8413
       have r₂ := eq66 x
       grind)
    | exact resolve eq8413 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8413
  have eq45419 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq407 y x
       have i₂ := eq8414
       grind)
    | exact superpose eq8414 eq407
    | exact resolve eq407 eq8414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8414
  have eq82165 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq407 (σ y) (σ x)
       have i₂ := eq45419
       grind)
    | exact superpose eq45419 eq407
    | exact resolve eq407 eq45419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45419
  have eq82219 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq82165
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq82165
    | exact resolve eq82165 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82165
  have eq82775 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq914 y
       have i₂ := eq82219
       grind)
    | exact superpose eq82219 eq914
    | (have r₁ := eq914 y
       have r₂ := eq82219
       grind)
    | exact resolve eq914 eq82219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq82219
  have eq82907 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq82775
  have eq82963 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq82907
       have i₂ := eq43 y
       grind)
    | exact superpose eq43 eq82907
    | exact resolve eq82907 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq82907
  have eq82964 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq82963
  have eq83455 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq82964
       grind)
    | exact superpose eq82964 eq10
    | exact resolve eq10 eq82964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82964
  have eq83694 : x = y ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq83455
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq83455
    | exact resolve eq83455 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83455
  have eq84397 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83694
       grind)
    | exact superpose eq83694 eq16
    | exact resolve eq16 eq83694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83694
  have eq84398 : (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq84397
       have r₂ := eq66 x
       grind)
    | exact resolve eq84397 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq84397
  have eq84871 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq91 y X0
       have i₂ := eq84398
       grind)
    | exact superpose eq84398 eq91
    | exact resolve eq91 eq84398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq84897 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq84398
       grind)
    | exact superpose eq84398 eq10
    | exact resolve eq10 eq84398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84398
  have eq85139 : y = (M.op y y) := by
    first
    | (have i₁ := eq84897
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq84897
    | exact resolve eq84897 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84897
  have eq85705 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq362 y X0
       have i₂ := eq85139
       grind)
    | exact superpose eq85139 eq362
    | exact resolve eq362 eq85139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq85824 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq517 y y x
       have i₂ := eq85139
       grind)
    | exact superpose eq85139 eq517
    | exact resolve eq517 eq85139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85139
  have eq85859 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq85824 X0
       have i₂ := eq407 y X0
       grind)
    | exact superpose eq407 eq85824
    | exact resolve eq85824 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407 eq85824
  have eq88762 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq85705 X0
       have i₂ := eq85859 X0
       grind)
    | exact superpose eq85859 eq85705
    | exact resolve eq85705 eq85859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85705
  have eq89349 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq85859 X0
       have i₂ := eq88762 X0
       grind)
    | exact superpose eq88762 eq85859
    | exact resolve eq85859 eq88762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85859
  have eq89499 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq517 y X1 X0
       have i₂ := eq88762 X0
       grind)
    | exact superpose eq88762 eq517
    | exact resolve eq517 eq88762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq89671 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq89499 X0 X0
       have i₂ := eq88762 X0
       grind)
    | exact superpose eq88762 eq89499
    | exact resolve eq89499 eq88762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88762 eq89499
  have eq118276 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq84871 X0
       have i₂ := eq89671 X0 (σ y)
       grind)
    | exact superpose eq89671 eq84871
    | exact resolve eq84871 eq89671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84871
  have eq118923 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq89671 X0 (σ y)
       have i₂ := eq118276 X0
       grind)
    | exact superpose eq118276 eq89671
    | exact resolve eq89671 eq118276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89671 eq118276
  have eq125918 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq118923 (σ x)
       grind)
    | exact superpose eq118923 eq16
    | exact resolve eq16 eq118923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118923
  have eq126190 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq125918
       have i₂ := eq89349 x
       grind)
    | exact superpose eq89349 eq125918
    | exact resolve eq125918 eq89349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89349 eq125918
  have eq126191 : False := by grind
  exact eq126191

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq43 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq43 (σ X0)
       grind)
    | exact superpose eq43 eq15
    | exact resolve eq15 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq19
    | exact resolve eq19 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq57
    | exact resolve eq57 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq63
    | exact resolve eq63 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq79 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq10
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq153 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq183 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq116 (τ X0)
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq116
    | exact resolve eq116 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq116
  have eq201 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq9
    | exact resolve eq9 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq348 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (M.op (σ X0) (σ X0))) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq201 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq201
    | exact resolve eq201 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq360 : ∀ X0 X1 : G, (M.op (M.op (M.op (τ (σ (M.op X0 X0))) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq348 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq348
    | exact resolve eq348 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq362 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq360 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq360
    | exact resolve eq360 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq401 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq362 (σ X0) X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq362
    | exact resolve eq362 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq362 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq362
    | exact resolve eq362 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X2
       have i₂ := eq407 X0 X1
       grind)
    | exact superpose eq407 eq9
    | exact resolve eq9 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq153
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq153
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq153
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq153
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq153 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq662 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq661
  have eq800 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq362 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq401 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq401 eq362
    | exact resolve eq362 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq905 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq800 X0
       grind)
    | exact superpose eq800 eq12
    | exact resolve eq12 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq914 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq905 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq905
    | (have j0 := eq905 X0
       grind)
    | exact resolve eq905 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq8413 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq662
       grind)
    | exact superpose eq662 eq16
    | exact resolve eq16 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq8414 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq8413
       have r₂ := eq66 x
       grind)
    | exact resolve eq8413 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8413
  have eq45419 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq407 y x
       have i₂ := eq8414
       grind)
    | exact superpose eq8414 eq407
    | exact resolve eq407 eq8414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8414
  have eq82165 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq407 (σ y) (σ x)
       have i₂ := eq45419
       grind)
    | exact superpose eq45419 eq407
    | exact resolve eq407 eq45419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45419
  have eq82219 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq82165
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq82165
    | exact resolve eq82165 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82165
  have eq82775 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq914 y
       have i₂ := eq82219
       grind)
    | exact superpose eq82219 eq914
    | (have r₁ := eq914 y
       have r₂ := eq82219
       grind)
    | exact resolve eq914 eq82219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq82219
  have eq82907 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq82775
  have eq82963 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq82907
       have i₂ := eq43 y
       grind)
    | exact superpose eq43 eq82907
    | exact resolve eq82907 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq82907
  have eq82964 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq82963
  have eq83455 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq82964
       grind)
    | exact superpose eq82964 eq10
    | exact resolve eq10 eq82964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82964
  have eq83694 : x = y ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq83455
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq83455
    | exact resolve eq83455 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83455
  have eq84397 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83694
       grind)
    | exact superpose eq83694 eq16
    | exact resolve eq16 eq83694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83694
  have eq84398 : (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq84397
       have r₂ := eq66 x
       grind)
    | exact resolve eq84397 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq84397
  have eq84871 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq91 y X0
       have i₂ := eq84398
       grind)
    | exact superpose eq84398 eq91
    | exact resolve eq91 eq84398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq84897 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq84398
       grind)
    | exact superpose eq84398 eq10
    | exact resolve eq10 eq84398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84398
  have eq85139 : y = (M.op y y) := by
    first
    | (have i₁ := eq84897
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq84897
    | exact resolve eq84897 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84897
  have eq85705 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq362 y X0
       have i₂ := eq85139
       grind)
    | exact superpose eq85139 eq362
    | exact resolve eq362 eq85139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq85824 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq517 y y x
       have i₂ := eq85139
       grind)
    | exact superpose eq85139 eq517
    | exact resolve eq517 eq85139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85139
  have eq85859 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq85824 X0
       have i₂ := eq407 y X0
       grind)
    | exact superpose eq407 eq85824
    | exact resolve eq85824 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407 eq85824
  have eq88762 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq85705 X0
       have i₂ := eq85859 X0
       grind)
    | exact superpose eq85859 eq85705
    | exact resolve eq85705 eq85859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85705
  have eq89349 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq85859 X0
       have i₂ := eq88762 X0
       grind)
    | exact superpose eq88762 eq85859
    | exact resolve eq85859 eq88762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85859
  have eq89499 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op y X1) X0) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq517 y X1 X0
       have i₂ := eq88762 X0
       grind)
    | exact superpose eq88762 eq517
    | exact resolve eq517 eq88762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq89671 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq89499 X0 X0
       have i₂ := eq88762 X0
       grind)
    | exact superpose eq88762 eq89499
    | exact resolve eq89499 eq88762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88762 eq89499
  have eq118276 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq84871 X0
       have i₂ := eq89671 X0 (σ y)
       grind)
    | exact superpose eq89671 eq84871
    | exact resolve eq84871 eq89671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84871
  have eq118923 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq89671 X0 (σ y)
       have i₂ := eq118276 X0
       grind)
    | exact superpose eq118276 eq89671
    | exact resolve eq89671 eq118276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89671 eq118276
  have eq125918 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq118923 (σ x)
       grind)
    | exact superpose eq118923 eq16
    | exact resolve eq16 eq118923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118923
  have eq126190 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq125918
       have i₂ := eq89349 x
       grind)
    | exact superpose eq89349 eq125918
    | exact resolve eq125918 eq89349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89349 eq125918
  have eq126191 : False := by grind
  exact eq126191

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
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
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq80 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq125 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 (k X1 (τ X0)) X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq58
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq16
    | (have j1 := eq58 x y
       grind)
    | exact resolve eq16 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq246 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq80 (τ X0)
       grind)
    | exact superpose eq80 eq34
    | exact resolve eq34 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq247 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq246 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq246
    | exact resolve eq246 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq261 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq247 (τ X0)
       grind)
    | exact superpose eq247 eq19
    | exact resolve eq19 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq271 : ∀ X0 : G, (k (σ (σ (M.op (τ (τ X0)) (τ (τ X0))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq261 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq261
    | exact resolve eq261 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq308 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63
    | exact resolve eq63 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = (M.op X0 X0) ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq63 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X0)
       have r₂ := eq63 X0 (τ X0)
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq63 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq325 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq327 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = (M.op X0 X0) ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq314 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq328 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq327 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq329 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq325 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq325
    | (have j0 := eq325 X0
       grind)
    | exact resolve eq325 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq335 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq308
    | (have j0 := eq308 X0 X1
       grind)
    | exact resolve eq308 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq427 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))
       have i₂ := eq271 (τ X0)
       grind)
    | exact superpose eq271 eq19
    | exact resolve eq19 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 : G, (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq427 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq427
    | exact resolve eq427 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq650 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) X2) ∨ (σ X0) = (k (k (σ X1) X2) (σ X0)) ∨ (M.op (k (σ X1) X2) (σ X0)) = (σ (k (k X1 (τ X2)) X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (σ X1) X2) (σ X0)
       have i₂ := eq125 X1 X2 X0
       grind)
    | exact superpose eq125 eq13
    | (have j0 := eq13 (k (σ X1) X2) (σ X0)
       have j1 := eq125 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq125 X0 X1 X2
       grind)
    | exact resolve eq13 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq658 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) X2) ∨ (σ X0) = (k (k (σ X1) X2) (σ X0)) ∨ (M.op (k (σ X1) X2) (σ X0)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq650 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq659 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (k (σ X1) X2) ∨ (σ X0) = (k (k (σ X1) X2) (σ X0)) ∨ (M.op (k (σ X1) X2) (σ X0)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq658 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq660 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k (k X1 (τ X2)) X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) X2) ∨ (M.op (k (σ X1) X2) (σ X0)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq659 X0 X1 X2
       have i₂ := eq30 X1 X2 X0
       grind)
    | exact superpose eq30 eq659
    | (have j0 := eq659 X0 X1 X2
       grind)
    | exact resolve eq659 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq659
  have eq3829 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq329 X0
       grind)
    | exact superpose eq329 eq10
    | (have j1 := eq329 X0
       grind)
    | exact resolve eq10 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq6992 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq3829
  have eq7065 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6992 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq6992
    | (have j0 := eq6992 X0
       grind)
    | exact resolve eq6992 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq6992
  have eq7066 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7065 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7065
  have eq7155 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7066 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7066
    | exact resolve eq7066 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7240 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq7155 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq7155
    | exact resolve eq7155 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq7155
  have eq7246 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq7240 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7240
    | exact resolve eq7240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7240
  have eq7403 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7246 (σ X0)
       grind)
    | exact superpose eq7246 eq15
    | exact resolve eq15 eq7246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7449 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7403 X0
       have i₂ := eq7246 X0
       grind)
    | exact superpose eq7246 eq7403
    | exact resolve eq7403 eq7246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7403
  have eq7680 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq328 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq328
    | exact resolve eq328 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq7764 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7680 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7680
    | (have j0 := eq7680 X0 X1
       grind)
    | exact resolve eq7680 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7680
  have eq8160 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq80 (σ X0)
       have i₂ := eq7449 X0
       grind)
    | exact superpose eq7449 eq80
    | exact resolve eq80 eq7449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38200 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k (k X1 (τ X2)) X0)) ∨ (k (σ X1) X2) = (σ (M.op X0 X0)) ∨ (M.op (k (σ X1) X2) (σ X0)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq660 X0 X1 X2
       have i₂ := eq7449 X0
       grind)
    | exact superpose eq7449 eq660
    | (have j0 := eq660 X0 X1 X2
       grind)
    | exact resolve eq660 eq7449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq38229 : ∀ X0 X1 : G, (σ X1) = (σ (k (τ X0) X1)) ∨ (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) = (σ (M.op X1 X1)) ∨ (σ (k (τ X0) X1)) = (M.op (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38200 X0 (σ (σ (M.op (τ (τ (τ x))) (τ (τ (τ x)))))) x
       have i₂ := eq271 (τ x)
       grind)
    | exact superpose eq271 eq38200
    | (have j0 := eq38200 X1 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))) X0
       grind)
    | exact resolve eq38200 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq38200
  have eq38504 : ∀ X0 X1 : G, (σ X1) = (k X0 (σ X1)) ∨ (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) = (σ (M.op X1 X1)) ∨ (σ (k (τ X0) X1)) = (M.op (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38229 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq38229
    | (have j0 := eq38229 X0 X1
       grind)
    | exact resolve eq38229 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38229
  have eq38599 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (k X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = (M.op (k (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))) X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38504 X0 X1
       have i₂ := eq438 X0
       grind)
    | exact superpose eq438 eq38504
    | (have j0 := eq38504 X0 X1
       grind)
    | exact resolve eq38504 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38504
  have eq38681 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38599 X0 X1
       have i₂ := eq438 X0
       grind)
    | exact superpose eq438 eq38599
    | (have j0 := eq38599 X0 X1
       grind)
    | exact resolve eq38599 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq38599
  have eq38747 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38681 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq38681
    | (have j0 := eq38681 X0 X1
       grind)
    | exact resolve eq38681 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq38681
  have eq55036 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (k X0 (τ X1)) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq7764 X0 (τ X1)
       grind)
    | exact superpose eq7764 eq19
    | (have j1 := eq7764 X0 (τ X1)
       grind)
    | exact resolve eq19 eq7764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7764
  have eq55217 : ∀ X0 X1 : G, (τ (k X1 X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55036 X0 X1
       have i₂ := eq7066 X1
       grind)
    | exact superpose eq7066 eq55036
    | (have j0 := eq55036 X0 X1
       grind)
    | exact resolve eq55036 eq7066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7066 eq55036
  have eq55250 : ∀ X0 X1 : G, (τ X1) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55217 X0 X1
       have i₂ := eq7246 X1
       grind)
    | exact superpose eq7246 eq55217
    | (have j0 := eq55217 X0 X1
       grind)
    | exact resolve eq55217 eq7246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7246 eq55217
  have eq725401 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38747 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38747
  have eq1767043 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ X1) X0) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq55250 X1 X0
       grind)
    | exact superpose eq55250 eq19
    | (have j1 := eq55250 X1 X0
       grind)
    | exact resolve eq19 eq55250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq55250
  have eq1768014 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1767043 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1767043
    | (have j0 := eq1767043 X0 X1
       grind)
    | exact resolve eq1767043 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767043
  have eq1769828 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 (τ (σ X1)))) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1768014 (σ X1) X0
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1768014
    | (have j0 := eq1768014 (σ X1) X0
       grind)
    | exact resolve eq1768014 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1768014
  have eq1770700 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1769828 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1769828
    | (have j0 := eq1769828 X0 X1
       grind)
    | exact resolve eq1769828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1769828
  have eq1770966 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1770700 X0 X1
       have i₂ := eq7449 X1
       grind)
    | exact superpose eq7449 eq1770700
    | (have j0 := eq1770700 X0 X1
       grind)
    | exact resolve eq1770700 eq7449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770700
  have eq1771213 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1770966 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq1770966
    | (have j0 := eq1770966 X0 X1
       grind)
    | exact resolve eq1770966 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770966
  have eq1773749 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq1771213 x y
       grind)
    | exact superpose eq1771213 eq129
    | (have j1 := eq1771213 x y
       grind)
    | (have r₁ := eq129
       have r₂ := eq1771213 x y
       grind)
    | exact resolve eq129 eq1771213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1771213
  have eq1774685 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq1773749
  have eq1774747 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq141 x y
       grind)
    | (have r₁ := eq1774685
       have r₂ := eq141 x y
       grind)
    | exact resolve eq1774685 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1774685
  have eq1774983 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1774747
       have i₂ := eq7449 y
       grind)
    | exact superpose eq7449 eq1774747
    | exact resolve eq1774747 eq7449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7449 eq1774747
  have eq1779794 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq8160 y
       have i₂ := eq1774983
       grind)
    | exact superpose eq1774983 eq8160
    | exact resolve eq8160 eq1774983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774983
  have eq1780800 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1779794
  have eq1780925 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8160 y
       have i₂ := eq1780800
       grind)
    | exact superpose eq1780800 eq8160
    | exact resolve eq8160 eq1780800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8160 eq1780800
  have eq1781997 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1780925
  have eq1782011 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1781997
       grind)
    | exact superpose eq1781997 eq16
    | exact resolve eq16 eq1781997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1782319 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq725401 (σ x) y
       have i₂ := eq1781997
       grind)
    | exact superpose eq1781997 eq725401
    | (have j0 := eq725401 (σ x) y
       grind)
    | (have r₁ := eq725401 (σ x) y
       have r₂ := eq1781997
       grind)
    | exact resolve eq725401 eq1781997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725401 eq1781997
  have eq1783084 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq1782319
  have eq1783124 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq1783084
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1783084
    | exact resolve eq1783084 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783084
  have eq1803220 : (M.op y y) = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1783124
       grind)
    | exact superpose eq1783124 eq10
    | exact resolve eq10 eq1783124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783124
  have eq1804218 : (σ y) = (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1803220
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1803220
    | exact resolve eq1803220 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803220
  have eq1805949 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq335 x y
       have i₂ := eq1804218
       grind)
    | exact superpose eq1804218 eq335
    | (have j0 := eq335 x y
       grind)
    | exact resolve eq335 eq1804218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335 eq1804218
  have eq1806999 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1805949
  have eq1807063 : y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1806999
       have r₂ := eq1782011
       grind)
    | exact resolve eq1806999 eq1782011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1806999
  have eq1813313 : (σ y) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1782011
       have i₂ := eq1807063
       grind)
    | exact superpose eq1807063 eq1782011
    | exact resolve eq1782011 eq1807063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807063
  have eq1814085 : x = (M.op y y) := by grind
  clear eq1813313
  have eq1814097 : y = (M.op x y) := by
    first
    | (have i₁ := eq80 y
       have i₂ := eq1814085
       grind)
    | exact superpose eq1814085 eq80
    | exact resolve eq80 eq1814085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1814085
  have eq1818191 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1782011
       have i₂ := eq1814097
       grind)
    | exact superpose eq1814097 eq1782011
    | exact resolve eq1782011 eq1814097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782011 eq1814097
  have eq1818962 : False := by grind
  exact eq1818962

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyy_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
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
  have eq64 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq65 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq119 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq160 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq119 eq16
    | exact resolve eq16 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq210 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq215 : y ≠ y ∨ (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ y = (k (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq210 eq12
    | (have j0 := eq12 (M.op (M.op x y) (M.op x y)) y
       grind)
    | (have r₁ := eq12 (M.op (M.op x y) (M.op x y)) y
       have r₂ := eq210
       grind)
    | exact resolve eq12 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : y = (k (M.op (M.op x y) (M.op x y)) y) ∨ (M.op y y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq215
  have eq522 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq530 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq522 X0
       grind)
    | exact superpose eq522 eq14
    | exact resolve eq14 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq806 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq807 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq72 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq808 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq807 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq899 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq50 eq530
    | exact resolve eq530 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq901 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq51 eq530
    | exact resolve eq530 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq530
  have eq932 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq899 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq899
       grind)
    | exact resolve eq12 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq942 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq932
  have eq945 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq901 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq901
       grind)
    | exact resolve eq12 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq955 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq945
  have eq3676 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq808 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq808
    | (have j0 := eq808 (τ X0)
       grind)
    | exact resolve eq808 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq808
  have eq3684 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3676 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3676
    | (have j0 := eq3676 X0
       grind)
    | exact resolve eq3676 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3676
  have eq3690 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3684 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3684
    | (have j0 := eq3684 X0
       grind)
    | exact resolve eq3684 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3684
  have eq7530 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7531 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq7530
    | exact resolve eq7530 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7530
  have eq7542 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq7531
       have r₂ := eq28
       grind)
    | exact resolve eq7531 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7531
  have eq7544 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq7542
    | exact resolve eq7542 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7542
  have eq7548 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq7544 eq522
    | exact resolve eq522 eq7544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7544
  have eq7569 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq7548
    | exact resolve eq7548 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7548
  have eq7570 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7569
  have eq7573 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq522 y
       have i₂ := eq7570
       grind)
    | exact superpose eq7570 eq522
    | exact resolve eq522 eq7570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7570
  have eq7594 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7573
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq7573
    | exact resolve eq7573 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7573
  have eq7595 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq7594
  have eq7596 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7595 eq28
    | exact resolve eq28 eq7595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7625 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7595 eq955
    | exact resolve eq955 eq7595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq7595
  have eq7970 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7625 eq88
    | exact resolve eq88 eq7625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7625
  have eq7979 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq7970
  have eq7989 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq7979
       have r₂ := eq7596
       grind)
    | exact resolve eq7979 eq7596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7596 eq7979
  have eq7998 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq7989
  have eq8181 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7998 eq88
    | exact resolve eq88 eq7998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq7998
  have eq8191 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq8181
  have eq8205 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq522 y
       have i₂ := eq8191
       grind)
    | exact superpose eq8191 eq522
    | exact resolve eq522 eq8191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8191
  have eq8226 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq8205
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8205
    | exact resolve eq8205 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8205
  have eq8227 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq8226
  have eq8229 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8227 eq29
    | exact resolve eq29 eq8227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq8242 : (k x (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8227 eq64
    | exact resolve eq64 eq8227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq8227
  have eq8355 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq160 eq8242
    | exact resolve eq8242 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq8242
  have eq8360 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq8229
    | exact resolve eq8229 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq8229
  have eq9115 : (M.op x y) ≠ (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8355 eq3690
    | (have j0 := eq3690 (M.op x y)
       grind)
    | exact resolve eq3690 eq8355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3690 eq8355
  have eq45557 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq942 eq9115
    | (have r₁ := eq9115
       have r₂ := eq942
       grind)
    | exact resolve eq9115 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942 eq9115
  have eq45562 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq45557
  have eq51277 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq45562
  have eq51279 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq51277
       have r₂ := eq8360
       grind)
    | exact resolve eq51277 eq8360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8360 eq51277
  have eq51447 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51279 eq210
    | exact resolve eq210 eq51279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq51450 : y = (k x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51279 eq218
    | exact resolve eq218 eq51279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq51279
  have eq51518 : y = (k x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq51450
       have r₂ := eq65
       grind)
    | exact resolve eq51450 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq51450
  have eq51519 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51447
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51447
    | exact resolve eq51447 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq51447
  have eq51520 : y = (M.op x y) := by grind
  clear eq51519
  have eq51521 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq51520 eq21
    | exact resolve eq21 eq51520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq51520
  have eq51698 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq51521
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq51521
    | exact resolve eq51521 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51521
  have eq51699 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq51698 eq27
    | exact resolve eq27 eq51698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq51703 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq51698 eq48
    | exact resolve eq48 eq51698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq53802 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq806 x y
       have i₂ := eq51518
       grind)
    | exact superpose eq51518 eq806
    | (have j0 := eq806 x y
       grind)
    | exact resolve eq806 eq51518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806 eq51518
  have eq53803 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq53802
  have eq53808 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq53803
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq53803
    | exact resolve eq53803 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53803
  have eq53828 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq51698 eq53808
    | exact resolve eq53808 eq51698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53808
  have eq53846 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq53828
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq53828
    | exact resolve eq53828 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53828
  have eq53862 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq51699 eq53846
    | exact resolve eq53846 eq51699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53846
  have eq53871 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq53862
       have r₂ := eq28
       grind)
    | exact resolve eq53862 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53862
  have eq53880 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq53871
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq53871
    | exact resolve eq53871 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq53871
  have eq53889 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq51698 eq53880
    | exact resolve eq53880 eq51698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53880
  have eq53898 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq53889
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq53889
    | exact resolve eq53889 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53889
  have eq54014 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq53898 eq522
    | exact resolve eq522 eq53898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53898
  have eq54073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq51699 eq54014
    | exact resolve eq54014 eq51699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54014
  have eq54075 : x = (M.op y y) := by
    first
    | (have r₁ := eq54073
       have r₂ := eq28
       grind)
    | exact resolve eq54073 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54073
  have eq54079 : x = (k x y) := by grind
  clear eq54075
  have eq54149 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq54079
       grind)
    | exact superpose eq54079 eq45
    | exact resolve eq45 eq54079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq54079
  have eq54187 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq51698 eq54149
    | exact resolve eq54149 eq51698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51698 eq54149
  have eq54205 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq54187
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq54187
    | exact resolve eq54187 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq54187
  have eq54368 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq54205 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq54205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54205
  have eq54383 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq51699 eq54368
    | exact resolve eq54368 eq51699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54368
  have eq54398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq51699 eq54383
    | exact resolve eq54383 eq51699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54383
  have eq54409 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq54398
       have r₂ := eq28
       grind)
    | exact resolve eq54398 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54398
  have eq54708 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54409 eq522
    | exact resolve eq522 eq54409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq54409
  have eq54767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51699 eq54708
    | exact resolve eq54708 eq51699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54708
  have eq54769 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq54767
       have r₂ := eq28
       grind)
    | exact resolve eq54767 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54767
  have eq54806 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq54769 eq901
    | exact resolve eq901 eq54769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq54915 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq54806 eq51703
    | exact resolve eq51703 eq54806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51703
  have eq54999 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq54769 eq54915
    | exact resolve eq54915 eq54769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54769 eq54915
  have eq55029 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq54806 eq54999
    | exact resolve eq54999 eq54806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54806 eq54999
  have eq55051 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51699 eq55029
    | exact resolve eq55029 eq51699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51699 eq55029
  have eq55069 : False := by grind
  exact eq55069
