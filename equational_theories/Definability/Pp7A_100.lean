import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pyx_pxy_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 (k X0 X1) (M.op X1 X0)
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
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
  clear eq37
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq16 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X2 X2) (M.op (k X3 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X0 X1 X2 X3
       have i₂ := eq175 X3
       grind)
    | exact superpose eq175 eq176
    | exact resolve eq176 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq181 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X0)) = (M.op (k X2 X2) (M.op (k X3 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq179 X0 X1 X2 X3
       have i₂ := eq175 X2
       grind)
    | exact superpose eq175 eq179
    | exact resolve eq179 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq182 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (k X0 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (σ (k X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 (σ X0) X1 X2
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq182
    | exact resolve eq182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq589 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq589
    | exact resolve eq589 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq1133 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op y y) := by
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
  have eq1134 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq1136 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1134
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq1134
    | exact resolve eq1134 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq1137 : (M.op x y) = (k x y) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1133
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq1133
    | exact resolve eq1133 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1188 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1137
       grind)
    | exact superpose eq1137 eq41
    | exact resolve eq41 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1137
  have eq1189 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1188
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1188
    | exact resolve eq1188 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1191 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq20 eq1189
    | exact resolve eq1189 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq1191 eq1136
    | exact resolve eq1136 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136 eq1191
  have eq1201 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | (have r₁ := eq1194
       have r₂ := eq27
       grind)
    | exact resolve eq1194 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1205 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq1201 eq116
    | exact resolve eq116 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1201
  have eq1222 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq30 eq1205
    | exact resolve eq1205 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1223 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1222
  have eq1236 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x X1))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq182 y X0 X1
       have i₂ := eq1223
       grind)
    | exact superpose eq1223 eq182
    | exact resolve eq182 eq1223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1239 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (σ x) X1))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq564 y X0 X1
       have i₂ := eq1223
       grind)
    | exact superpose eq1223 eq564
    | exact resolve eq564 eq1223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq1223
  have eq1244 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (σ x) X1))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1239 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1239
    | (have j0 := eq1239 X0 X1
       grind)
    | exact resolve eq1239 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq1486 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1236 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1236
    | (have j0 := eq1236 X0 y
       grind)
    | exact resolve eq1236 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1645 : y = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1486 sF0
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq1486
    | exact resolve eq1486 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486
  have eq1732 : y = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1645
       have i₂ := eq590 sF0
       grind)
    | exact superpose eq590 eq1645
    | exact resolve eq1645 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1799 : (σ y) = (k (σ (k (M.op x y) (M.op x y))) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1732 eq42
    | exact resolve eq42 eq1732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732
  have eq1800 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq42 eq1799
    | exact resolve eq1799 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq1799
  have eq1801 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq1800
    | exact resolve eq1800 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq1802 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1801
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1801
    | exact resolve eq1801 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq1913 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26 eq1244
    | (have j0 := eq1244 X0 (σ y)
       grind)
    | exact resolve eq1244 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq2082 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4⟩ := hcon
    have f2082_15 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x X1))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
      intro X0 X1
      grind
    have f2082_16 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
      intro X0
      grind
    have f2082_24 : (M.op (σ x) (σ y)) ≠ (M.op x (σ y)) := by grind
    have f2082_27 : (σ x) ≠ (σ y) := by grind
    have f2082_28 : x ≠ y := by grind
    have f2082_31 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) ∨ x = y := by
      intro X0
      first
      | (have j0 := f2082_16 X0
         grind)
      | (have r₁ := f2082_16 X0
         have r₂ := f2082_27
         grind)
      | exact resolve f2082_16 f2082_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2082_32 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x X1))) = X1 ∨ x = y := by
      intro X0 X1
      first
      | (have j0 := f2082_15 X0 X1
         grind)
      | (have r₁ := f2082_15 X0 X1
         have r₂ := f2082_27
         grind)
      | exact resolve f2082_15 f2082_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2082_33 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) := by
      intro X0
      first
      | (have j0 := f2082_31 X0
         grind)
      | (have r₁ := f2082_31 X0
         have r₂ := f2082_28
         grind)
      | exact resolve f2082_31 f2082_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2082_34 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x X1))) = X1 := by
      intro X0 X1
      first
      | (have j0 := f2082_32 X0 X1
         grind)
      | (have r₁ := f2082_32 X0 X1
         have r₂ := f2082_28
         grind)
      | exact resolve f2082_32 f2082_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2082_115 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
      first
      | (have i₁ := f2082_34 x (M.op (σ x) (σ y))
         have i₂ := f2082_33 x
         grind)
      | exact superpose f2082_33 f2082_34
      | exact resolve f2082_34 f2082_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2082_128 : False := by
      first
      | (have r₁ := f2082_115
         have r₂ := f2082_24
         grind)
      | exact resolve f2082_115 f2082_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f2082_128
  clear eq1913
  have eq2106 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2082
  have eq2291 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X1 X0 x x
       have i₂ := eq181 X1 X2 x x
       grind)
    | (have i₁ := eq181 X0 X1 X2 X2
       have i₂ := eq181 X0 (k X2 X2) X2 x
       grind)
    | exact superpose eq181 eq181
    | exact resolve eq181 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq2594 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op X0 X1))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1236 x X1
       have i₂ := eq2291 x X1 X0
       grind)
    | (have i₁ := eq1236 x X1
       have i₂ := eq2291 X0 X1 x
       grind)
    | exact superpose eq2291 eq1236
    | exact resolve eq1236 eq2291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236 eq2291
  have eq4195 : ∀ X0 : G, (M.op x (M.op X0 (k X0 X0))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2594 X0 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq2594
    | exact resolve eq2594 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594
  have eq4436 : ∀ X0 : G, (M.op x (k (k X0 X0) X0)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4195 X0
       have i₂ := eq590 X0
       grind)
    | exact superpose eq590 eq4195
    | exact resolve eq4195 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq4195
  have eq6409 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1802 eq4436
    | exact resolve eq4436 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802 eq4436
  have eq6426 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6409
  have eq6444 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6426 eq2106
    | exact resolve eq2106 eq6426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2106 eq6426
  have eq6460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6444
  have eq6471 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq6460
       have r₂ := eq27
       grind)
    | exact resolve eq6460 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6460
  have eq6482 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq6471 eq32
    | exact resolve eq32 eq6471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq6471
  have eq6522 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq6482
    | exact resolve eq6482 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq6482
  have eq6523 : x = y := by grind
  clear eq6522
  have eq6525 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6523
       grind)
    | exact superpose eq6523 eq18
    | exact resolve eq18 eq6523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6526 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq6523
       grind)
    | exact superpose eq6523 eq24
    | exact resolve eq24 eq6523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq6523
  have eq6540 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq6526
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6526
    | exact resolve eq6526 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6526
  have eq6541 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq6525
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq6525
    | exact resolve eq6525 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6525
  have eq6542 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6540 eq26
    | exact resolve eq26 eq6540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6540
  have eq6578 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6542
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq6542
    | exact resolve eq6542 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq6542
  have eq6583 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq6541
       grind)
    | exact superpose eq6541 eq40
    | exact resolve eq40 eq6541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq6541
  have eq6618 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq6583
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6583
    | exact resolve eq6583 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6583
  have eq6621 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6578 eq6618
    | exact resolve eq6618 eq6578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6578 eq6618
  have eq6623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq6621
    | exact resolve eq6621 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6621
  have eq6625 : False := by grind
  exact eq6625

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq76 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq85
  have eq374 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq387 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq374 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq391 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq387 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq387 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq387 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq401 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq391 X0 X1
       have j1 := eq76 X0 (σ X1)
       grind)
    | (have r₁ := eq391 X0 X1
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq391 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq391
  have eq408 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq401 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq401
    | (have j0 := eq401 X0 X1
       grind)
    | exact resolve eq401 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq409 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq408 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq413 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq409 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq409
    | exact resolve eq409 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq409 x y
       grind)
    | exact superpose eq409 eq16
    | exact resolve eq16 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq512 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq413 X0 (τ X1)
       grind)
    | exact superpose eq413 eq17
    | exact resolve eq17 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq413
  have eq530 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq512 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq512
    | exact resolve eq512 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq539 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq530 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq530
    | exact resolve eq530 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq558 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq424
       have i₂ := eq539 x y
       grind)
    | exact superpose eq539 eq424
    | exact resolve eq424 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424 eq539
  have eq559 : False := by grind
  exact eq559

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  have eq67 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq70 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (k y x) := by
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
  have eq71 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq16
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq88 y x
       grind)
    | exact superpose eq88 eq67
    | (have j1 := eq88 y x
       grind)
    | exact resolve eq67 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq88 sF3 sF2
       grind)
    | exact superpose eq88 eq77
    | (have j1 := eq88 (σ y) (σ x)
       grind)
    | exact resolve eq77 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq110 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq107
    | exact resolve eq107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq112 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq110
    | exact resolve eq110 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq114 eq88
    | (have j0 := eq88 (σ y) (σ x)
       grind)
    | exact resolve eq88 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq117
    | exact resolve eq117 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq121 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq118
       have r₂ := eq27
       grind)
    | exact resolve eq118 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq123 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq123 eq27
    | exact resolve eq27 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq22 eq37
  have eq144 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq133 eq16
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq424 : (k (σ y) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq112
       grind)
    | exact superpose eq112 eq67
    | exact resolve eq67 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq427 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq424
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq424
    | exact resolve eq424 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq475 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq123 eq71
    | (have r₁ := eq71
       have r₂ := eq123
       grind)
    | exact resolve eq71 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq123
  have eq476 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq475
  have eq481 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq476 eq114
    | exact resolve eq114 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq485 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq481
  have eq492 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq485
       have r₂ := eq125
       grind)
    | exact resolve eq485 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq485
  have eq497 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq492 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq492
       grind)
    | exact resolve eq13 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq499 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq497 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq499 eq114
    | exact resolve eq114 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq499
  have eq560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq557
  have eq565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq560
    | exact resolve eq560 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq560
  have eq567 : y = (M.op x y) := by
    first
    | (have r₁ := eq565
       have r₂ := eq27
       grind)
    | exact resolve eq565 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq569 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq567 eq20
    | exact resolve eq20 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq572 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq567 eq70
    | (have r₁ := eq70
       have r₂ := eq567
       grind)
    | exact resolve eq70 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq578 : x = (M.op x x) ∨ y = (k y x) := by grind
  clear eq572
  have eq586 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq569
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq569
    | exact resolve eq569 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq672 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq586 eq427
    | exact resolve eq427 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq675 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq672
       have r₂ := eq27
       grind)
    | exact resolve eq672 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq687 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq675 eq144
    | exact resolve eq144 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq675
  have eq690 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq567 eq687
    | exact resolve eq687 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq867 : x = (M.op x x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq578
       have i₂ := eq690
       grind)
    | exact superpose eq690 eq578
    | exact resolve eq578 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578 eq690
  have eq868 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq867
       grind)
    | exact superpose eq867 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq867
       grind)
    | exact resolve eq13 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq875 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq868 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq2011 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq112
       have i₂ := eq875 y
       grind)
    | exact superpose eq875 eq112
    | exact resolve eq112 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq875
  have eq2028 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2011
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2011
    | exact resolve eq2011 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2011
  have eq2034 : y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq567 eq2028
    | exact resolve eq2028 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq2028
  have eq2035 : y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2034
  have eq2044 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq586 eq2035
    | exact resolve eq2035 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035
  have eq2048 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq2044
       have r₂ := eq27
       grind)
    | exact resolve eq2044 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2044
  have eq2056 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2048 eq15
    | exact resolve eq15 eq2048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048
  have eq2077 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2056
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2056
    | exact resolve eq2056 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2056
  have eq2083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq586 eq2077
    | exact resolve eq2077 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586 eq2077
  have eq2087 : False := by grind
  exact eq2087

/-- `Equation826`: `x = x ◇ ((x ◇ y) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation826 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law826 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law826.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X1 X1))) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq267 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq270 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq268 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq268 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq281 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq270 (σ X0)
       grind)
    | exact superpose eq270 eq15
    | exact resolve eq15 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq281
    | exact resolve eq281 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq281
  have eq344 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq9
    | exact resolve eq9 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq345 X0 X1
       have j1 := eq346 X0 X1
       grind)
    | (have r₁ := eq345 X0 X1
       have r₂ := eq346 X0 X1
       grind)
    | exact resolve eq345 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq346
  have eq349 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq344 X0
       have i₂ := eq300 (M.op X0 X0)
       grind)
    | exact superpose eq300 eq344
    | exact resolve eq344 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq451 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq348 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq348
    | exact resolve eq348 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) X2) = X2 ∨ (k X2 (k X0 (σ X1))) = (M.op (k X0 (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq348 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq348
    | exact resolve eq348 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq461 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq348 X0 X1
       grind)
    | exact superpose eq348 eq22
    | (have j1 := eq348 X0 X1
       grind)
    | exact resolve eq22 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq462 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq348 X0 (σ X1)
       grind)
    | exact superpose eq348 eq15
    | (have j1 := eq348 X0 (σ X1)
       grind)
    | exact resolve eq15 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq491 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq451 (τ X0) X1
       grind)
    | exact superpose eq451 eq18
    | (have j1 := eq451 (τ X0) X1
       grind)
    | exact resolve eq18 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq451
  have eq585 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (M.op (M.op X0 X0) (M.op X0 X0)))) X0) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq461 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq349 X0
       grind)
    | exact superpose eq349 eq461
    | exact resolve eq461 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq612 : ∀ X0 : G, (τ (σ X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq585 X0
       have i₂ := eq10 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq10 eq585
    | (have j0 := eq585 X0
       grind)
    | exact resolve eq585 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq617 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq612 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq612
    | (have j0 := eq612 X0
       grind)
    | exact resolve eq612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq669 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq491 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq491
    | exact resolve eq491 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq729 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq669 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq669
    | (have j0 := eq669 X0 X1
       grind)
    | exact resolve eq669 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq1093 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq462 x y
       grind)
    | exact superpose eq462 eq16
    | (have j1 := eq462 x y
       grind)
    | exact resolve eq16 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1120 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq462 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq11339 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (k X0 (k X1 (σ X2))) = X0 ∨ (k X0 (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (k X1 (σ X2))
       have i₂ := eq452 X1 X2 X0
       grind)
    | exact superpose eq452 eq13
    | (have j0 := eq13 X0 (k X1 (σ X2))
       have j1 := eq452 X1 X2 (k X1 (σ X2))
       grind)
    | (have r₁ := eq13 X2 (k X0 (σ X1))
       have r₂ := eq452 X0 X1 X2
       grind)
    | exact resolve eq13 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq11364 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (k X0 (k X1 (σ X2))) = X0 ∨ (k X0 (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq11339 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11339
  have eq11385 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op (k X1 (σ X2)) X0) ∨ (k X0 (k X1 (σ X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq11364 X0 X1 X2
       have j1 := eq12 X0 (k X1 (σ X2))
       grind)
    | (have r₁ := eq11364 X0 X1 X2
       have r₂ := eq12 X0 (k X1 (σ X2))
       grind)
    | exact resolve eq11364 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11364
  have eq12448 : ∀ X0 X1 X2 : G, (k X1 (k X2 X0)) = (M.op (k X2 X0) X1) ∨ (k X1 (k X2 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11385 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11385
    | exact resolve eq11385 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11385
  have eq23902 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq349 X0
       have i₂ := eq617 X0
       grind)
    | exact superpose eq617 eq349
    | (have j1 := eq617 X0
       grind)
    | exact resolve eq349 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq617
  have eq24010 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23902 X0
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq23902
    | (have j0 := eq23902 X0
       grind)
    | exact resolve eq23902 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq23902
  have eq24198 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq24010 X0
       grind)
    | exact superpose eq24010 eq10
    | (have j1 := eq24010 X0
       grind)
    | exact resolve eq10 eq24010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24010
  have eq24292 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24198 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24198
    | (have j0 := eq24198 X0
       grind)
    | exact resolve eq24198 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24198
  have eq24383 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12448 X0 X1 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq24292 X0
       grind)
    | exact superpose eq24292 eq12448
    | (have j1 := eq24292 X0
       grind)
    | exact resolve eq12448 eq24292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12448 eq24292
  have eq24489 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq24383 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq24383 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq24383 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24383
  have eq24858 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1093
       have i₂ := eq24489 x y
       grind)
    | exact superpose eq24489 eq1093
    | (have j1 := eq24489 x y
       grind)
    | exact resolve eq1093 eq24489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq24859 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq24489 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24489
  have eq24860 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24858
  have eq25003 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1120 x y
       have i₂ := eq24860
       grind)
    | exact superpose eq24860 eq1120
    | (have j0 := eq1120 x y
       grind)
    | exact resolve eq1120 eq24860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120 eq24860
  have eq25038 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25003
  have eq25039 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25038
  have eq25046 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25039
       grind)
    | exact superpose eq25039 eq16
    | exact resolve eq16 eq25039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25063 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq24859 (σ y) (σ x)
       have i₂ := eq25039
       grind)
    | exact superpose eq25039 eq24859
    | (have j0 := eq24859 (σ y) (σ x)
       grind)
    | (have r₁ := eq24859 (σ y) (σ x)
       have r₂ := eq25039
       grind)
    | exact resolve eq24859 eq25039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24859 eq25039
  have eq25064 : (σ y) = (k (σ y) (σ x)) := by grind
  clear eq25063
  have eq25074 : (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq25064
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq25064
    | exact resolve eq25064 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25064
  have eq25104 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq729 x y
       have i₂ := eq25074
       grind)
    | exact superpose eq25074 eq729
    | (have j0 := eq729 x y
       grind)
    | exact resolve eq729 eq25074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729 eq25074
  have eq25209 : y = (M.op x y) := by
    first
    | (have r₁ := eq25104
       have r₂ := eq25046
       grind)
    | exact resolve eq25104 eq25046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25104
  have eq25271 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq25046
       have i₂ := eq25209
       grind)
    | exact superpose eq25209 eq25046
    | exact resolve eq25046 eq25209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25046 eq25209
  have eq25295 : False := by grind
  exact eq25295

/-- `Equation826`: `x = x ◇ ((x ◇ y) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation826 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law826 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law826.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq58 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq24
  have eq59 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq58
    | (have j0 := eq58 X0
       grind)
    | exact resolve eq58 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = X0 := by
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
  clear eq18
  have eq87 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq54 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq54 X0
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq54 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq90 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq87 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq87 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq196 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq16
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq371 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | (have j0 := eq79 X1 X1
       grind)
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq401 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq371 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq371
    | (have j0 := eq371 X0 X1
       grind)
    | exact resolve eq371 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq688 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq196
       have i₂ := eq401 y x
       grind)
    | exact superpose eq401 eq196
    | (have j1 := eq401 (σ x) (σ y)
       grind)
    | (have r₁ := eq196
       have r₂ := eq401 y x
       grind)
    | (have r₁ := eq196
       have r₂ := eq401 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq196
       have r₂ := eq401 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq196 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq401
  have eq689 : x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq688
  have eq691 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq708 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq691 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq691
    | (have j0 := eq691 X0
       grind)
    | exact resolve eq691 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq691
  have eq711 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq708 X0
       grind)
    | exact superpose eq708 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq708 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq708 X0
       grind)
    | exact resolve eq12 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq718 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq711 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq804 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq718 X0 X1
       grind)
    | exact superpose eq718 eq11
    | (have j1 := eq718 X0 X1
       grind)
    | exact resolve eq11 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq816 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq804 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq804
    | (have j0 := eq804 X0 X0
       grind)
    | exact resolve eq804 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq859 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq816 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq860 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq859 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq927 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq860 X0
       grind)
    | exact superpose eq860 eq89
    | (have j0 := eq89 X0
       grind)
    | exact resolve eq89 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq928 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq860 X0
       grind)
    | exact superpose eq860 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq943 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq860 (σ X0)
       grind)
    | exact superpose eq860 eq15
    | exact resolve eq15 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq962 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq943 X0
       have i₂ := eq860 X0
       grind)
    | exact superpose eq860 eq943
    | exact resolve eq943 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq943
  have eq15413 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq689
       grind)
    | exact superpose eq689 eq16
    | exact resolve eq16 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq15414 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq15413
       have r₂ := eq962 x
       grind)
    | exact resolve eq15413 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15413
  have eq15415 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15414
       have i₂ := eq962 x
       grind)
    | exact superpose eq962 eq15414
    | exact resolve eq15414 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15414
  have eq15417 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15415
       grind)
    | exact superpose eq15415 eq10
    | exact resolve eq10 eq15415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15415
  have eq15515 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15417
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15417
    | exact resolve eq15417 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15417
  have eq15734 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15515
       grind)
    | exact superpose eq15515 eq16
    | exact resolve eq16 eq15515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15515
  have eq15735 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15734
       have r₂ := eq962 x
       grind)
    | exact resolve eq15734 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15734
  have eq15743 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq927 x
       have i₂ := eq15735
       grind)
    | exact superpose eq15735 eq927
    | (have j0 := eq927 x
       grind)
    | (have r₁ := eq927 x
       have r₂ := eq15735
       grind)
    | exact resolve eq927 eq15735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15744 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq928 x X0
       have i₂ := eq15735
       grind)
    | exact superpose eq15735 eq928
    | (have j0 := eq928 x X0
       grind)
    | (have r₁ := eq928 x x
       have r₂ := eq15735
       grind)
    | exact resolve eq928 eq15735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15735
  have eq15773 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq15744 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15744
  have eq15774 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq15743
  have eq15780 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq15773 X0
       have j1 := eq928 x X0
       grind)
    | (have r₁ := eq15773 X0
       have r₂ := eq928 x x
       grind)
    | exact resolve eq15773 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq15773
  have eq15781 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq927 x
       grind)
    | (have r₁ := eq15774
       have r₂ := eq927 x
       grind)
    | exact resolve eq15774 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927 eq15774
  have eq15782 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq15781
       have i₂ := eq962 x
       grind)
    | exact superpose eq962 eq15781
    | exact resolve eq15781 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962 eq15781
  have eq15944 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq15782
       grind)
    | exact superpose eq15782 eq10
    | exact resolve eq10 eq15782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15782
  have eq16049 : x = (M.op x x) := by
    first
    | (have i₁ := eq15944
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15944
    | exact resolve eq15944 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15944
  have eq16082 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq16049
       grind)
    | exact superpose eq16049 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq16049
       grind)
    | exact resolve eq12 eq16049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16049
  have eq16120 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq16082 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16082
  have eq16592 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq15780 (σ X0)
       grind)
    | exact superpose eq15780 eq15
    | exact resolve eq15 eq15780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15780
  have eq16660 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq16592 X0
       have i₂ := eq16120 X0
       grind)
    | exact superpose eq16120 eq16592
    | exact resolve eq16592 eq16120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16120 eq16592
  have eq17335 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16660 y
       grind)
    | exact superpose eq16660 eq16
    | (have r₁ := eq16
       have r₂ := eq16660 y
       grind)
    | exact resolve eq16 eq16660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16660
  have eq17413 : False := by grind
  exact eq17413

/-- `Equation826`: `x = x ◇ ((x ◇ y) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation826 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law826 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law826.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq529 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
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
  have eq532 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq3243 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq529 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq529
    | exact resolve eq529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq3295 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3243 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3243
    | (have j0 := eq3243 X0 X1
       grind)
    | exact resolve eq3243 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3243
  have eq3441 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq532 x y
       grind)
    | exact superpose eq532 eq16
    | (have j1 := eq532 x y
       grind)
    | exact resolve eq16 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3454 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq532 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6210 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3441
       have i₂ := eq3295 y x
       grind)
    | exact superpose eq3295 eq3441
    | (have j1 := eq3295 (σ x) (σ y)
       grind)
    | (have r₁ := eq3441
       have r₂ := eq3295 y x
       grind)
    | (have r₁ := eq3441
       have r₂ := eq3295 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3441
       have r₂ := eq3295 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3441 eq3295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3295
  have eq6211 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq6210
  have eq7563 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3454 X1 X0
       have i₂ := eq532 X0 X1
       grind)
    | exact superpose eq532 eq3454
    | (have j0 := eq3454 X0 X1
       have j1 := eq532 X0 X1
       grind)
    | (have r₁ := eq3454 X0 X0
       have r₂ := eq532 X0 X0
       grind)
    | exact resolve eq3454 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq7567 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7563 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7563
  have eq7571 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq7567 X0 X1
       have j1 := eq3454 X0 X1
       grind)
    | (have r₁ := eq7567 X0 X1
       have r₂ := eq3454 (k X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq7567 X0 X1
       have r₂ := eq3454 (k X1 X0) (k X0 X1)
       grind)
    | (have r₁ := eq7567 X0 X1
       have r₂ := eq3454 X0 X1
       grind)
    | exact resolve eq7567 eq3454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3454 eq7567
  have eq7944 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7571 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq7571
    | (have j0 := eq7571 (τ X0) (τ X1)
       grind)
    | exact resolve eq7571 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq8003 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7944 X0 X1
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq7944
    | (have j0 := eq7944 X0 X1
       grind)
    | exact resolve eq7944 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq7944
  have eq8069 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8003 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq8003
    | (have j0 := eq8003 X0 X1
       grind)
    | exact resolve eq8003 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8003
  have eq8119 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8069 X1 X0
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq8069
    | (have j0 := eq8069 X0 X1
       grind)
    | (have r₁ := eq8069 X1 X1
       have r₂ := eq11 (k X1 X1)
       grind)
    | exact resolve eq8069 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8069
  have eq8167 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8119 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq8119
    | (have j0 := eq8119 X0 X1
       grind)
    | exact resolve eq8119 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8119
  have eq8212 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8167 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8167
    | (have j0 := eq8167 X0 X1
       grind)
    | exact resolve eq8167 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8167
  have eq8242 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) ∨ X0 = X1 ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8212 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8212
    | (have j0 := eq8212 X0 X1
       grind)
    | exact resolve eq8212 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8212
  have eq8260 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8242 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8242
    | (have j0 := eq8242 X0 X1
       grind)
    | exact resolve eq8242 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8242
  have eq19100 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6211
       grind)
    | exact superpose eq6211 eq16
    | exact resolve eq16 eq6211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6211
  have eq19101 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq19100
       have r₂ := eq22 x
       grind)
    | exact resolve eq19100 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19100
  have eq19104 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19101
       grind)
    | exact superpose eq19101 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19101
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19101
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19101
       grind)
    | exact resolve eq13 eq19101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19101
  have eq19107 : x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq19104
  have eq19353 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19107
       grind)
    | exact superpose eq19107 eq16
    | exact resolve eq16 eq19107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19107
  have eq19354 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq19353
       have r₂ := eq22 x
       grind)
    | exact resolve eq19353 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19353
  have eq19359 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq19354
       grind)
    | exact superpose eq19354 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19354
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19354
       grind)
    | exact resolve eq13 eq19354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19360 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq19354
       grind)
    | exact superpose eq19354 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19354
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19354
       grind)
    | exact resolve eq13 eq19354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19354
  have eq19363 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq19360
  have eq19364 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq19363
  have eq19365 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x y) := by grind
  clear eq19359
  have eq19366 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x y) := by grind
  clear eq19365
  have eq19370 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq19364
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19364
    | exact resolve eq19364 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19364
  have eq19371 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq19366
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq19366
    | exact resolve eq19366 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19366
  have eq19409 : (σ (k x y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq19370
       have i₂ := eq19371
       grind)
    | exact superpose eq19371 eq19370
    | exact resolve eq19370 eq19371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19370 eq19371
  have eq19431 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by grind
  clear eq19409
  have eq19443 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq3441
       have i₂ := eq19431
       grind)
    | exact superpose eq19431 eq3441
    | exact resolve eq3441 eq19431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3441
  have eq19447 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by grind
  clear eq19443
  have eq19448 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by grind
  clear eq19447
  have eq19449 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq7571 x y
       grind)
    | (have r₁ := eq19448
       have r₂ := eq7571 x y
       grind)
    | (have r₁ := eq19448
       have r₂ := eq7571 y x
       grind)
    | exact resolve eq19448 eq7571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7571 eq19448
  have eq19455 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq19449
       grind)
    | exact superpose eq19449 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19449
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19449
       grind)
    | exact resolve eq13 eq19449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19449
  have eq19458 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq19455
  have eq19459 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq19458
  have eq19465 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19459
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19459
    | exact resolve eq19459 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19459
  have eq19471 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19465
       grind)
    | exact superpose eq19465 eq16
    | exact resolve eq16 eq19465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19465
  have eq19504 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq19471
       have i₂ := eq19431
       grind)
    | exact superpose eq19431 eq19471
    | exact resolve eq19471 eq19431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19431
  have eq19509 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by grind
  clear eq19504
  have eq19510 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by grind
  clear eq19509
  have eq19512 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19510
       grind)
    | exact superpose eq19510 eq10
    | exact resolve eq10 eq19510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19510
  have eq19681 : x = y ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq19512
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19512
    | exact resolve eq19512 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19512
  have eq19683 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19681
       grind)
    | exact superpose eq19681 eq16
    | exact resolve eq16 eq19681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19681
  have eq19684 : (σ (k x y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq19683
       have r₂ := eq22 x
       grind)
    | exact resolve eq19683 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19683
  have eq19697 : (k y x) = (τ (σ (k x y))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq19684
       grind)
    | exact superpose eq19684 eq10
    | exact resolve eq10 eq19684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19684
  have eq19868 : (k x y) = (k y x) := by
    first
    | (have i₁ := eq19697
       have i₂ := eq10 (k x y)
       grind)
    | exact superpose eq10 eq19697
    | exact resolve eq19697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19697
  have eq19899 : (k x y) ≠ (k x y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq8260 x y
       have i₂ := eq19868
       grind)
    | exact superpose eq19868 eq8260
    | (have j0 := eq8260 x y
       grind)
    | (have r₁ := eq8260 x y
       have r₂ := eq19868
       grind)
    | (have r₁ := eq8260 y x
       have r₂ := eq19868
       grind)
    | exact resolve eq8260 eq19868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8260 eq19868
  have eq19912 : (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq19899
  have eq19921 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19912
       grind)
    | exact superpose eq19912 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19912
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19912
       grind)
    | exact resolve eq13 eq19912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19912
  have eq19924 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq19921
  have eq19925 : x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq19924
  have eq20253 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19925
       grind)
    | exact superpose eq19925 eq16
    | exact resolve eq16 eq19925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19925
  have eq20254 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq20253
       have r₂ := eq22 x
       grind)
    | exact resolve eq20253 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20253
  have eq20259 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19471
       have i₂ := eq20254
       grind)
    | exact superpose eq20254 eq19471
    | exact resolve eq19471 eq20254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19471 eq20254
  have eq20266 : (σ x) = (σ y) := by grind
  clear eq20259
  have eq20267 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20266
       grind)
    | exact superpose eq20266 eq16
    | exact resolve eq16 eq20266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20268 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20266
       grind)
    | exact superpose eq20266 eq10
    | exact resolve eq10 eq20266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20266
  have eq20438 : x = y := by
    first
    | (have i₁ := eq20268
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20268
    | exact resolve eq20268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20268
  have eq20439 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq20267
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq20267
    | exact resolve eq20267 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20267
  have eq20440 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq20439
       have i₂ := eq20438
       grind)
    | exact superpose eq20438 eq20439
    | exact resolve eq20439 eq20438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20438 eq20439
  have eq20441 : False := by grind
  exact eq20441

/-- `Equation826`: `x = x ◇ ((x ◇ y) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation826 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law826 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law826.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq178 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq183 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq695 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq753 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq695
    | (have j0 := eq695 X0 X1
       grind)
    | exact resolve eq695 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq846 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq183 (τ X1) (τ X0)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq183
    | (have j0 := eq183 (τ X1) (τ X0)
       grind)
    | exact resolve eq183 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq854 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq846 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq846
    | (have j0 := eq846 X0 X1
       grind)
    | exact resolve eq846 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq857 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq854 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq854
    | (have j0 := eq854 X0 X1
       grind)
    | exact resolve eq854 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq859 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq857 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq857
    | (have j0 := eq857 X0 X1
       grind)
    | exact resolve eq857 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq860 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq859 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq859
    | (have j0 := eq859 X0 X1
       grind)
    | exact resolve eq859 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq861 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq860 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq860
    | (have j0 := eq860 X0 X1
       grind)
    | exact resolve eq860 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq862 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq861 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq861
    | (have j0 := eq861 X0 X1
       grind)
    | exact resolve eq861 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq1008 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq178
       have i₂ := eq753 x y
       grind)
    | exact superpose eq753 eq178
    | (have j1 := eq753 (σ x) (σ y)
       grind)
    | (have r₁ := eq178
       have r₂ := eq753 x y
       grind)
    | (have r₁ := eq178
       have r₂ := eq753 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq178
       have r₂ := eq753 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq178 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq753
  have eq1009 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1008
  have eq13675 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1009
       grind)
    | exact superpose eq1009 eq16
    | exact resolve eq16 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq13676 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13675
       have r₂ := eq22 x
       grind)
    | exact resolve eq13675 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13675
  have eq14001 : y ≠ y ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq13676
       grind)
    | exact superpose eq13676 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq13676
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq13676
       grind)
    | exact resolve eq13 eq13676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13676
  have eq14003 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14001
  have eq18346 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14003
       grind)
    | exact superpose eq14003 eq16
    | exact resolve eq16 eq14003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14003
  have eq18347 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have r₁ := eq18346
       have r₂ := eq22 x
       grind)
    | exact resolve eq18346 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18346
  have eq18657 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq18347
       grind)
    | exact superpose eq18347 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18347
       grind)
    | exact resolve eq13 eq18347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18347
  have eq18659 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq18657
  have eq18660 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq18659
  have eq18663 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq18660
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq18660
    | exact resolve eq18660 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18660
  have eq19037 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq183 x y
       have i₂ := eq18663
       grind)
    | exact superpose eq18663 eq183
    | (have j0 := eq183 x y
       grind)
    | (have r₁ := eq183 x y
       have r₂ := eq18663
       grind)
    | exact resolve eq183 eq18663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18663
  have eq19063 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq19037
  have eq19064 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq19063
  have eq19070 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq183 x y
       grind)
    | (have r₁ := eq19064
       have r₂ := eq183 x y
       grind)
    | exact resolve eq19064 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq19064
  have eq19074 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19070
       grind)
    | exact superpose eq19070 eq16
    | exact resolve eq16 eq19070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19080 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq19070
       grind)
    | exact superpose eq19070 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19070
       grind)
    | exact resolve eq13 eq19070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19070
  have eq19082 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq19080
  have eq19083 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq19082
  have eq19086 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq19083
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq19083
    | exact resolve eq19083 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19083
  have eq19399 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19086
       grind)
    | exact superpose eq19086 eq10
    | exact resolve eq10 eq19086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19086
  have eq19495 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq19399
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19399
    | exact resolve eq19399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19399
  have eq19950 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19495
       grind)
    | exact superpose eq19495 eq16
    | exact resolve eq16 eq19495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19495
  have eq19951 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq19950
       have r₂ := eq22 x
       grind)
    | exact resolve eq19950 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19950
  have eq19965 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq19951
       grind)
    | exact superpose eq19951 eq10
    | exact resolve eq10 eq19951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19951
  have eq20063 : y = (k y x) := by
    first
    | (have i₁ := eq19965
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq19965
    | exact resolve eq19965 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19965
  have eq20429 : y ≠ y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq862 y x
       have i₂ := eq20063
       grind)
    | exact superpose eq20063 eq862
    | (have j0 := eq862 y x
       grind)
    | (have r₁ := eq862 y x
       have r₂ := eq20063
       grind)
    | exact resolve eq862 eq20063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862 eq20063
  have eq20444 : y = (M.op x y) ∨ x = y := by grind
  clear eq20429
  have eq20449 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19074
       have i₂ := eq20444
       grind)
    | exact superpose eq20444 eq19074
    | exact resolve eq19074 eq20444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19074 eq20444
  have eq20459 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq20449
  have eq20833 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20459
       grind)
    | exact superpose eq20459 eq16
    | exact resolve eq16 eq20459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20459
  have eq20838 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq20833
       have r₂ := eq22 x
       grind)
    | exact resolve eq20833 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20833
  have eq20839 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20838
       grind)
    | exact superpose eq20838 eq16
    | exact resolve eq16 eq20838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20840 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20838
       grind)
    | exact superpose eq20838 eq10
    | exact resolve eq10 eq20838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20838
  have eq20936 : x = y := by
    first
    | (have i₁ := eq20840
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20840
    | exact resolve eq20840 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20840
  have eq20937 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq20839
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq20839
    | exact resolve eq20839 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20839
  have eq20940 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq20937
       have i₂ := eq20936
       grind)
    | exact superpose eq20936 eq20937
    | exact resolve eq20937 eq20936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20936 eq20937
  have eq20941 : False := by grind
  exact eq20941

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_y_pxy_y_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq285 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq285 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq288 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq286 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq286 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq286 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq299 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq288 (σ X0)
       grind)
    | exact superpose eq288 eq15
    | exact resolve eq15 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq299 X0
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq299
    | exact resolve eq299 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq299
  have eq365 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq9
    | exact resolve eq9 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq366 X0 X1
       have j1 := eq368 X0 X1
       grind)
    | (have r₁ := eq366 X0 X1
       have r₂ := eq368 X0 X1
       grind)
    | exact resolve eq366 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq368
  have eq576 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq369 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq369
    | exact resolve eq369 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq369 X0 (σ X1)
       grind)
    | exact superpose eq369 eq15
    | (have j1 := eq369 X0 (σ X1)
       grind)
    | exact resolve eq15 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq657 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq576 (τ X0) X1
       grind)
    | exact superpose eq576 eq17
    | (have j1 := eq576 (τ X0) X1
       grind)
    | exact resolve eq17 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq576
  have eq908 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq657 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq657
    | exact resolve eq657 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq979 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq908 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq908
    | (have j0 := eq908 X0 X1
       grind)
    | exact resolve eq908 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq1594 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq582 x y
       grind)
    | exact superpose eq582 eq16
    | (have j1 := eq582 x y
       grind)
    | exact resolve eq16 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1631 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq582 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq1807 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1594
       have i₂ := eq979 x y
       grind)
    | exact superpose eq979 eq1594
    | (have j1 := eq979 (σ x) (σ y)
       grind)
    | (have r₁ := eq1594
       have r₂ := eq979 x y
       grind)
    | exact resolve eq1594 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1808 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1807
  have eq1813 : y ≠ y ∨ x = (M.op x x) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1808
       grind)
    | exact superpose eq1808 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1808
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1808
       grind)
    | exact resolve eq13 eq1808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1808
  have eq1818 : y = (k x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1813
  have eq3159 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1631 x y
       have i₂ := eq1818
       grind)
    | exact superpose eq1818 eq1631
    | (have j0 := eq1631 x y
       grind)
    | exact resolve eq1631 eq1818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631 eq1818
  have eq3168 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq3159
  have eq3169 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq3168
  have eq3175 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3169
       grind)
    | exact superpose eq3169 eq16
    | exact resolve eq16 eq3169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3181 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3169
       grind)
    | exact superpose eq3169 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3169
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq3169
       grind)
    | exact resolve eq13 eq3169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3169
  have eq3189 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq3181
  have eq3191 : (σ x) = (σ (M.op x x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3189
       have i₂ := eq318 x
       grind)
    | exact superpose eq318 eq3189
    | exact resolve eq3189 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq3189
  have eq3193 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3191
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3191
    | exact resolve eq3191 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3191
  have eq5591 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq979 x y
       have i₂ := eq3193
       grind)
    | exact superpose eq3193 eq979
    | (have j0 := eq979 x y
       grind)
    | exact resolve eq979 eq3193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq3193
  have eq5653 : y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq5591
       have r₂ := eq3175
       grind)
    | exact resolve eq5591 eq3175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5591
  have eq5686 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3175
       have i₂ := eq5653
       grind)
    | exact superpose eq5653 eq3175
    | exact resolve eq3175 eq5653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3175 eq5653
  have eq5709 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq5686
  have eq5710 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq5709
  have eq5728 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq5710
       grind)
    | exact superpose eq5710 eq10
    | exact resolve eq10 eq5710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5710
  have eq5793 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5728
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5728
    | exact resolve eq5728 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5728
  have eq5794 : x = (M.op x x) := by grind
  clear eq5793
  have eq5800 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq5794
       grind)
    | exact superpose eq5794 eq12
    | (have j0 := eq12 x X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq5794
       grind)
    | exact resolve eq12 eq5794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5855 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have j0 := eq5800 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5800
  have eq5899 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1594
       have i₂ := eq5855 y
       grind)
    | exact superpose eq5855 eq1594
    | exact resolve eq1594 eq5855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594 eq5855
  have eq5917 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5899
  have eq5935 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5917
       grind)
    | exact superpose eq5917 eq16
    | exact resolve eq16 eq5917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5939 : (σ x) = (M.op (σ x) (M.op (σ (M.op x x)) (σ y))) := by
    first
    | (have i₁ := eq365 x (σ y)
       have i₂ := eq5917
       grind)
    | exact superpose eq5917 eq365
    | exact resolve eq365 eq5917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq5970 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5939
       have i₂ := eq5794
       grind)
    | exact superpose eq5794 eq5939
    | exact resolve eq5939 eq5794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5939
  have eq5976 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5970
       have i₂ := eq5917
       grind)
    | exact superpose eq5917 eq5970
    | exact resolve eq5970 eq5917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5970
  have eq6316 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq5917
       have i₂ := eq5976
       grind)
    | exact superpose eq5976 eq5917
    | exact resolve eq5917 eq5976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5917 eq5976
  have eq6413 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6316
       grind)
    | exact superpose eq6316 eq10
    | exact resolve eq10 eq6316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6316
  have eq6488 : x = y := by
    first
    | (have i₁ := eq6413
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6413
    | exact resolve eq6413 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6413
  have eq6565 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5935
       have i₂ := eq6488
       grind)
    | exact superpose eq6488 eq5935
    | exact resolve eq5935 eq6488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5935 eq6488
  have eq6572 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq6565
       have i₂ := eq5794
       grind)
    | exact superpose eq5794 eq6565
    | exact resolve eq6565 eq5794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5794 eq6565
  have eq6573 : False := by grind
  exact eq6573
