import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation8`: `x = x ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation8 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law8 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law8.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq26 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq25
    | exact resolve eq25 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq25 X1 (τ X0)
       grind)
    | exact superpose eq25 eq16
    | (have j1 := eq25 X1 (τ X0)
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq26 (σ X1) (σ X0)
       grind)
    | exact superpose eq26 eq13
    | (have j1 := eq26 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq27 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq27
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq27 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq27 x y
       grind)
    | exact superpose eq27 eq14
    | (have j1 := eq27 x y
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq9
    | (have j1 := eq27 X0 X1
       grind)
    | exact resolve eq9 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq393 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq443 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq393 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq393
    | (have j0 := eq393 X0 X1
       grind)
    | exact resolve eq393 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq464 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq504 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq464
    | (have j0 := eq464 X0 X1
       grind)
    | exact resolve eq464 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq548 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1
       have i₂ := eq443 X0 X1
       grind)
    | (have i₁ := eq8 X0
       have i₂ := eq443 (M.op X0 X0) X1
       grind)
    | exact superpose eq443 eq8
    | (have j1 := eq443 X0 X1
       grind)
    | exact resolve eq8 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq823 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8 (σ X0)
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq8
    | (have j1 := eq38 X0 X0
       grind)
    | exact resolve eq8 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1160 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq548 y x
       grind)
    | exact superpose eq548 eq119
    | (have j1 := eq548 y x
       grind)
    | (have r₁ := eq119
       have r₂ := eq548 y x
       grind)
    | exact resolve eq119 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq1161 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq504 x y
       grind)
    | exact superpose eq504 eq119
    | (have j1 := eq504 x y
       grind)
    | (have r₁ := eq119
       have r₂ := eq504 x y
       grind)
    | exact resolve eq119 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq1162 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq119
       have i₂ := eq443 y x
       grind)
    | exact superpose eq443 eq119
    | (have j1 := eq443 (σ y) (σ x)
       grind)
    | (have r₁ := eq119
       have r₂ := eq443 y x
       grind)
    | exact resolve eq119 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq443
  have eq1163 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1162
  have eq1164 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq1161
  have eq1165 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1160
  have eq1179 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  have eq1180 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 (σ x)
       have i₂ := eq1163
       grind)
    | exact superpose eq1163 eq8
    | exact resolve eq8 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1183 : (σ y) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1179
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1179
    | exact resolve eq1179 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1224 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq1241 : (k x y) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1183
       grind)
    | exact superpose eq1183 eq9
    | exact resolve eq9 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1282 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1241
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1241
    | exact resolve eq1241 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1333 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1282
       grind)
    | exact superpose eq1282 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq1340 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1333
  have eq1436 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq107
    | (have j0 := eq107 X1 (τ X0)
       grind)
    | exact resolve eq107 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1532 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1436 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1436
    | (have j0 := eq1436 X0 X1
       grind)
    | exact resolve eq1436 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1436
  have eq1540 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1532 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1532
    | (have j0 := eq1532 X0 X1
       grind)
    | exact resolve eq1532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532
  have eq1858 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq1164
  have eq1862 : (σ y) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1858
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1858
    | exact resolve eq1858 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858
  have eq2004 : (k x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq1862
       grind)
    | exact superpose eq1862 eq9
    | exact resolve eq9 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq2049 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq2004
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2004
    | exact resolve eq2004 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004
  have eq2050 : y = (k x y) := by grind
  clear eq2049
  have eq2313 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26 y x
       have i₂ := eq2050
       grind)
    | exact superpose eq2050 eq26
    | (have j0 := eq26 y x
       grind)
    | exact resolve eq26 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2535 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq2313
  have eq3735 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124 x x
       have i₂ := eq1165
       grind)
    | exact superpose eq1165 eq124
    | exact resolve eq124 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq1165
  have eq3750 : x = y ∨ (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3735
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3735
    | exact resolve eq3735 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3735
  have eq3751 : (σ y) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3750
       have r₂ := eq2535
       grind)
    | exact resolve eq3750 eq2535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3750
  have eq4135 : (k x x) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq3751
       grind)
    | exact superpose eq3751 eq9
    | exact resolve eq9 eq3751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3751
  have eq4194 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4135
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4135
    | exact resolve eq4135 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4135
  have eq4667 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25 x x
       have i₂ := eq4194
       grind)
    | exact superpose eq4194 eq25
    | exact resolve eq25 eq4194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4194
  have eq4674 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq4667
       have r₂ := eq2535
       grind)
    | exact resolve eq4667 eq2535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4667
  have eq5565 : x = y ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1340
       have i₂ := eq4674
       grind)
    | exact superpose eq4674 eq1340
    | exact resolve eq1340 eq4674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340 eq4674
  have eq5568 : y = (M.op x x) ∨ x = y := by grind
  clear eq5565
  have eq5987 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8 x
       have i₂ := eq5568
       grind)
    | exact superpose eq5568 eq8
    | exact resolve eq8 eq5568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5568
  have eq5989 : x = (M.op x y) := by
    first
    | (have r₁ := eq5987
       have r₂ := eq2535
       grind)
    | exact resolve eq5987 eq2535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2535 eq5987
  have eq7494 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1180
       grind)
    | exact superpose eq1180 eq14
    | exact resolve eq14 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq7504 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7494
       have i₂ := eq5989
       grind)
    | exact superpose eq5989 eq7494
    | exact resolve eq7494 eq5989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7494
  have eq7505 : y = (M.op x x) := by grind
  clear eq7504
  have eq7860 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1224 x y
       have i₂ := eq2050
       grind)
    | exact superpose eq2050 eq1224
    | (have j0 := eq1224 x y
       grind)
    | exact resolve eq1224 eq2050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq8267 : y = (M.op x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq2050
       have i₂ := eq1540 x y
       grind)
    | exact superpose eq1540 eq2050
    | (have j1 := eq1540 x y
       grind)
    | exact resolve eq2050 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540 eq2050
  have eq8364 : x = y ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq8267
       have i₂ := eq5989
       grind)
    | exact superpose eq5989 eq8267
    | exact resolve eq8267 eq5989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8267
  have eq8365 : y = (k x x) ∨ x = y := by grind
  clear eq8364
  have eq11234 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq823 x
       have i₂ := eq8365
       grind)
    | exact superpose eq8365 eq823
    | exact resolve eq823 eq8365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823 eq8365
  have eq11299 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq11234
       have r₂ := eq7860
       grind)
    | exact resolve eq11234 eq7860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11234
  have eq11343 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq11299
       grind)
    | exact superpose eq11299 eq14
    | exact resolve eq14 eq11299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11299
  have eq11369 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq11343
       have i₂ := eq5989
       grind)
    | exact superpose eq5989 eq11343
    | exact resolve eq11343 eq5989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5989 eq11343
  have eq11370 : x = y := by grind
  clear eq11369
  have eq11419 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq11370
       grind)
    | exact superpose eq11370 eq14
    | exact resolve eq14 eq11370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11440 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7860
       have i₂ := eq11370
       grind)
    | exact superpose eq11370 eq7860
    | exact resolve eq7860 eq11370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7860
  have eq11443 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq11440
  have eq11451 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11419
       have i₂ := eq7505
       grind)
    | exact superpose eq7505 eq11419
    | exact resolve eq11419 eq7505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7505 eq11419
  have eq11453 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq11451
       have i₂ := eq11443
       grind)
    | exact superpose eq11443 eq11451
    | exact resolve eq11451 eq11443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11443 eq11451
  have eq11456 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq11453
       have i₂ := eq11370
       grind)
    | exact superpose eq11370 eq11453
    | exact resolve eq11453 eq11370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11370 eq11453
  have eq11457 : False := by grind
  exact eq11457

/-- `Equation10`: `x = x ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_pyx_pxy_Equation10 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law10 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law10.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X0) X0
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq93 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq306 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (σ X1) (σ X1)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq93
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq93 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq307 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq93 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq308 : ∀ X0 X1 : G, (σ X0) = (k (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq306 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq312 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq13 X1 X1
       grind)
    | exact superpose eq13 eq308
    | (have j0 := eq308 X0 X1
       grind)
    | exact resolve eq308 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq319 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 X1
       have i₂ := eq307 X1
       grind)
    | exact superpose eq307 eq312
    | (have j0 := eq312 X0 X1
       grind)
    | exact resolve eq312 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq326 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq307 (σ X0)
       grind)
    | exact superpose eq307 eq13
    | exact resolve eq13 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq326 X0
       have i₂ := eq307 X0
       grind)
    | exact superpose eq307 eq326
    | exact resolve eq326 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq326
  have eq479 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (σ X0) (σ X0)
       have i₂ := eq333 X0
       grind)
    | exact superpose eq333 eq16
    | exact resolve eq16 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq848 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq10
    | (have j1 := eq44 X1 X0
       grind)
    | exact resolve eq10 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq25946 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq848 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq848
    | (have j0 := eq848 X1 (σ X0)
       grind)
    | exact resolve eq848 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq26335 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25946 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq25946
    | (have j0 := eq25946 X0 X1
       grind)
    | exact resolve eq25946 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25946
  have eq30879 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq319 x y
       grind)
    | exact superpose eq319 eq14
    | (have j1 := eq319 x y
       grind)
    | exact resolve eq14 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq30948 : (σ x) = (σ (M.op y y)) := by
    first
    | (have j1 := eq26335 x y
       grind)
    | (have r₁ := eq30879
       have r₂ := eq26335 x y
       grind)
    | exact resolve eq30879 eq26335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26335 eq30879
  have eq31534 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq479 y
       have i₂ := eq30948
       grind)
    | exact superpose eq30948 eq479
    | exact resolve eq479 eq30948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq31537 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq30948
       grind)
    | exact superpose eq30948 eq9
    | exact resolve eq9 eq30948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30948
  have eq31690 : x = (M.op y y) := by
    first
    | (have i₁ := eq31537
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq31537
    | exact resolve eq31537 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31537
  have eq32052 : x = (M.op x y) := by
    first
    | (have i₁ := eq16 y y
       have i₂ := eq31690
       grind)
    | exact superpose eq31690 eq16
    | exact resolve eq16 eq31690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq31690
  have eq32624 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31534
       grind)
    | exact superpose eq31534 eq14
    | exact resolve eq14 eq31534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31534
  have eq32656 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq32624
       have i₂ := eq32052
       grind)
    | exact superpose eq32052 eq32624
    | exact resolve eq32624 eq32052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32052 eq32624
  have eq32657 : False := by grind
  exact eq32657

/-- `Equation11`: `x = x ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation11 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law11 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law11.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X1)
       have i₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact superpose eq8 eq11
    | (have r₁ := eq11 X0 (M.op X1 X1)
       have r₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq18 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq24 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq30 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq16
    | exact resolve eq16 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq28 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq28 eq13
    | (have j1 := eq28 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq128 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq26 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq250 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31
    | (have j0 := eq31 X0 X1
       grind)
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq285 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq250
    | (have j0 := eq250 X0 X1
       grind)
    | exact resolve eq250 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq803 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X1 X1
       have i₂ := eq285 X0 X1
       grind)
    | exact superpose eq285 eq30
    | (have j1 := eq285 X2 X0
       grind)
    | exact resolve eq30 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq285
  have eq1350 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq128 (M.op X0 X0)
       have i₂ := eq19 X0 (M.op X0 X0)
       grind)
    | exact superpose eq19 eq128
    | (have j0 := eq128 (M.op X0 X0)
       grind)
    | exact resolve eq128 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1364 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq128 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq128
    | (have j0 := eq128 (τ X0)
       grind)
    | exact resolve eq128 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq128
  have eq1376 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1350 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350
  have eq1381 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1364 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1364
    | (have j0 := eq1364 X0
       grind)
    | exact resolve eq1364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364
  have eq1390 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1381 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1381
    | (have j0 := eq1381 X0
       grind)
    | exact resolve eq1381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1448 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ (M.op X0 X0))
       have i₂ := eq1376 X0
       grind)
    | exact superpose eq1376 eq8
    | exact resolve eq8 eq1376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq2060 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq94 x y X0
       grind)
    | exact superpose eq94 eq14
    | (have j1 := eq94 X0 y X0
       grind)
    | exact resolve eq14 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq2125 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq2060 X0
       have j1 := eq803 y X0 x
       grind)
    | (have r₁ := eq2060 X0
       have r₂ := eq803 y x x
       grind)
    | exact resolve eq2060 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq2060
  have eq2167 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0 (σ y)
       have i₂ := eq2125 (σ X0)
       grind)
    | exact superpose eq2125 eq41
    | exact resolve eq41 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq2125
  have eq2173 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq2167 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2167
    | exact resolve eq2167 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167
  have eq2315 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1390 y
       have i₂ := eq2173 y
       grind)
    | exact superpose eq2173 eq1390
    | (have j0 := eq1390 y
       grind)
    | (have r₁ := eq1390 y
       have r₂ := eq2173 y
       grind)
    | exact resolve eq1390 eq2173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390 eq2173
  have eq2331 : y = (M.op y y) := by grind
  clear eq2315
  have eq2437 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 y
       have i₂ := eq2331
       grind)
    | exact superpose eq2331 eq8
    | exact resolve eq8 eq2331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2445 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1448 y X0
       have i₂ := eq2331
       grind)
    | exact superpose eq2331 eq1448
    | exact resolve eq1448 eq2331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448 eq2331
  have eq2763 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2445 (σ x)
       grind)
    | exact superpose eq2445 eq14
    | exact resolve eq14 eq2445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2445
  have eq2771 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2763
       have i₂ := eq2437 x
       grind)
    | exact superpose eq2437 eq2763
    | exact resolve eq2763 eq2437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2437 eq2763
  have eq2772 : False := by grind
  exact eq2772

/-- `Equation52`: `x = x ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation52 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law52 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law52.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op X0 X0) X0
       have i₂ := eq8 X0 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq16 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq26 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq33 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28
    | exact resolve eq28 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq35 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32
    | exact resolve eq32 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq24
    | exact resolve eq24 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq24 (τ X0) X1
       grind)
    | exact superpose eq24 eq19
    | (have j1 := eq24 (τ X0) X1
       grind)
    | exact resolve eq19 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24
  have eq63 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq33 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq33
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq92 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq94 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq40
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq92
    | exact resolve eq92 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq202 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (σ X1)
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq16
    | (have j1 := eq26 X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X1
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq106
    | (have j1 := eq26 X0 X1
       grind)
    | exact resolve eq106 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq106
  have eq246 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq225 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq225
    | (have j0 := eq225 X0 X1
       grind)
    | exact resolve eq225 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq261 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq22 X0 (σ X1)
       grind)
    | exact superpose eq22 eq40
    | (have j1 := eq22 X0 (σ X1)
       grind)
    | exact resolve eq40 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq40
  have eq564 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq637 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq564 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq564
    | (have j0 := eq564 X0 X1
       grind)
    | exact resolve eq564 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq663 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq706 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq663
    | (have j0 := eq663 X0 X1
       grind)
    | exact resolve eq663 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq760 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1
       have i₂ := eq637 X0 X1
       grind)
    | (have i₁ := eq16 X0
       have i₂ := eq637 (M.op X0 X0) X1
       grind)
    | exact superpose eq637 eq16
    | (have j1 := eq637 X0 X1
       grind)
    | exact resolve eq16 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq961 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (σ X0)
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq16
    | (have j1 := eq52 X0 X0
       grind)
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1439 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq202 x y
       grind)
    | exact superpose eq202 eq14
    | (have j1 := eq202 x y
       grind)
    | exact resolve eq14 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1453 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq2466 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq63
    | (have j0 := eq63 X1 (σ X0)
       grind)
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq2543 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2466 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2466
    | (have j0 := eq2466 X0 X1
       grind)
    | exact resolve eq2466 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466
  have eq7100 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq7125 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1453 (τ X1) (τ X0)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq1453
    | (have j0 := eq1453 (τ X1) (τ X0)
       grind)
    | exact resolve eq1453 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq7159 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7125 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq7125
    | (have j0 := eq7125 X0 X1
       grind)
    | exact resolve eq7125 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7125
  have eq7169 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7159 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7159
    | (have j0 := eq7159 X0 X1
       grind)
    | exact resolve eq7159 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7159
  have eq7172 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7169 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7169
    | (have j0 := eq7169 X0 X1
       grind)
    | exact resolve eq7169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7169
  have eq7173 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7172 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7172
    | (have j0 := eq7172 X0 X1
       grind)
    | exact resolve eq7172 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7172
  have eq11179 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq246 x y
       grind)
    | exact superpose eq246 eq14
    | (have j1 := eq246 x y
       grind)
    | exact resolve eq14 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq11218 : y = (k y x) := by
    first
    | (have j1 := eq706 x y
       grind)
    | (have r₁ := eq11179
       have r₂ := eq706 x y
       grind)
    | exact resolve eq11179 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq11179
  have eq11897 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq637 x y
       have i₂ := eq11218
       grind)
    | exact superpose eq11218 eq637
    | (have j0 := eq637 x y
       grind)
    | exact resolve eq637 eq11218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11898 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq760 x y
       have i₂ := eq11218
       grind)
    | exact superpose eq11218 eq760
    | (have j0 := eq760 x y
       grind)
    | exact resolve eq760 eq11218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11899 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1453 x y
       have i₂ := eq11218
       grind)
    | exact superpose eq11218 eq1453
    | (have j0 := eq1453 x y
       grind)
    | exact resolve eq1453 eq11218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453 eq11218
  have eq17714 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1439
       have i₂ := eq637 x y
       grind)
    | exact superpose eq637 eq1439
    | (have j1 := eq637 x y
       grind)
    | (have r₁ := eq1439
       have r₂ := eq637 x y
       grind)
    | exact resolve eq1439 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq17716 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1439
       have i₂ := eq760 x y
       grind)
    | exact superpose eq760 eq1439
    | (have j1 := eq760 (σ x) (σ y)
       grind)
    | (have r₁ := eq1439
       have r₂ := eq760 x y
       grind)
    | exact resolve eq1439 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq1439
  have eq17720 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17716
  have eq17722 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq17714
  have eq17743 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17722
       grind)
    | exact superpose eq17722 eq14
    | exact resolve eq14 eq17722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17722
  have eq18124 : (σ x) ≠ (σ y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17743
       have i₂ := eq11897
       grind)
    | exact superpose eq11897 eq17743
    | exact resolve eq17743 eq11897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11897
  have eq18126 : (σ x) ≠ (σ y) ∨ x = (M.op y y) := by grind
  clear eq18124
  have eq18645 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17720
       grind)
    | exact superpose eq17720 eq14
    | exact resolve eq14 eq17720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18656 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94 (σ x) y
       have i₂ := eq17720
       grind)
    | exact superpose eq17720 eq94
    | (have j0 := eq94 (σ x) y
       grind)
    | exact resolve eq94 eq17720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq17720
  have eq18678 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18656
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq18656
    | exact resolve eq18656 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18656
  have eq18698 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq7173 y x
       grind)
    | (have r₁ := eq18678
       have r₂ := eq7173 y x
       grind)
    | exact resolve eq18678 eq7173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7173 eq18678
  have eq18737 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18645
       have i₂ := eq11898
       grind)
    | exact superpose eq11898 eq18645
    | exact resolve eq18645 eq11898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11898 eq18645
  have eq18740 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq18737
  have eq19545 : (τ (σ x)) = (k y (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq261 (σ y) y
       have i₂ := eq18698
       grind)
    | exact superpose eq18698 eq261
    | exact resolve eq261 eq18698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq18698
  have eq19582 : (τ (σ x)) = (k y (τ (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19545
       have r₂ := eq18740
       grind)
    | exact resolve eq19545 eq18740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18740 eq19545
  have eq19602 : (k y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19582
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq19582
    | exact resolve eq19582 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19582
  have eq19609 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19602
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq19602
    | exact resolve eq19602 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19602
  have eq19860 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2543 y y
       have i₂ := eq19609
       grind)
    | exact superpose eq19609 eq2543
    | exact resolve eq2543 eq19609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2543 eq19609
  have eq19870 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19860
       have r₂ := eq18126
       grind)
    | exact resolve eq19860 eq18126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18126 eq19860
  have eq20544 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq19870
       grind)
    | exact superpose eq19870 eq16
    | exact resolve eq16 eq19870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq19870
  have eq20563 : x = (M.op x y) := by grind
  clear eq20544
  have eq20976 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17743
       have i₂ := eq20563
       grind)
    | exact superpose eq20563 eq17743
    | exact resolve eq17743 eq20563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17743
  have eq20977 : ∀ X0 : G, (M.op y X0) = (k X0 y) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 y X0 x
       have i₂ := eq20563
       grind)
    | exact superpose eq20563 eq23
    | (have j0 := eq23 y X0 x
       grind)
    | exact resolve eq23 eq20563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq20988 : x = (M.op y y) := by grind
  clear eq20976
  have eq21546 : ∀ X0 : G, y = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq8 y X0
       have i₂ := eq20988
       grind)
    | exact superpose eq20988 eq8
    | exact resolve eq8 eq20988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27562 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq961 y
       have i₂ := eq20977 y
       grind)
    | exact superpose eq20977 eq961
    | (have j1 := eq20977 y
       grind)
    | exact resolve eq961 eq20977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq20977
  have eq27607 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq7100 y
       grind)
    | (have r₁ := eq27562
       have r₂ := eq7100 y
       grind)
    | exact resolve eq27562 eq7100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7100 eq27562
  have eq27612 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq27607
       have i₂ := eq20988
       grind)
    | exact superpose eq20988 eq27607
    | exact resolve eq27607 eq20988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27607
  have eq31615 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq27612
       grind)
    | exact superpose eq27612 eq14
    | exact resolve eq14 eq27612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27612
  have eq31659 : (σ x) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq31615
       have i₂ := eq20563
       grind)
    | exact superpose eq20563 eq31615
    | exact resolve eq31615 eq20563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20563 eq31615
  have eq31660 : y = (M.op y x) := by grind
  clear eq31659
  have eq32571 : y = (M.op y y) := by
    first
    | (have i₁ := eq21546 y
       have i₂ := eq31660
       grind)
    | exact superpose eq31660 eq21546
    | exact resolve eq21546 eq31660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21546
  have eq32592 : x = y := by
    first
    | (have i₁ := eq32571
       have i₂ := eq20988
       grind)
    | exact superpose eq20988 eq32571
    | exact resolve eq32571 eq20988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20988 eq32571
  have eq33253 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq32592
       grind)
    | exact superpose eq32592 eq14
    | exact resolve eq14 eq32592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33261 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11899
       have i₂ := eq32592
       grind)
    | exact superpose eq32592 eq11899
    | exact resolve eq11899 eq32592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11899
  have eq33296 : x = (M.op x x) := by
    first
    | (have i₁ := eq31660
       have i₂ := eq32592
       grind)
    | exact superpose eq32592 eq31660
    | exact resolve eq31660 eq32592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31660 eq32592
  have eq33306 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq33261
  have eq33310 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq33253
       have i₂ := eq33296
       grind)
    | exact superpose eq33296 eq33253
    | exact resolve eq33253 eq33296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33253 eq33296
  have eq33311 : False := by grind
  exact eq33311

/-- `Equation55`: `x = x ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation55 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law55 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law55.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op X0 X0) X0
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq17 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq25 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq35 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq20
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq20 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32
    | exact resolve eq32 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq24
    | exact resolve eq24 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq24 (τ X0) X1
       grind)
    | exact superpose eq24 eq20
    | (have j1 := eq24 (τ X0) X1
       grind)
    | exact resolve eq20 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq58 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq24 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq81 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X1) X0
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq8
    | (have j1 := eq25 X1 X0
       grind)
    | exact resolve eq8 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq86 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq88 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq12 (σ X1) X0
       grind)
    | exact superpose eq12 eq40
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq100 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq86
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq200 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (σ X1)
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq17
    | (have j1 := eq26 X0 X1
       grind)
    | exact resolve eq17 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq100 X1
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq100
    | (have j1 := eq26 X0 X1
       grind)
    | exact resolve eq100 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq100
  have eq244 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq226
    | (have j0 := eq226 X0 X1
       grind)
    | exact resolve eq226 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq578 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq654 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq578
    | (have j0 := eq578 X0 X1
       grind)
    | exact resolve eq578 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq679 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq726 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq679 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq679
    | (have j0 := eq679 X0 X1
       grind)
    | exact resolve eq679 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq780 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1
       have i₂ := eq654 X0 X1
       grind)
    | (have i₁ := eq17 X0
       have i₂ := eq654 (M.op X0 X0) X1
       grind)
    | exact superpose eq654 eq17
    | (have j1 := eq654 X0 X1
       grind)
    | exact resolve eq17 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1066 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17 (σ X0)
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq17
    | (have j1 := eq52 X0 X0
       grind)
    | exact resolve eq17 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq52
  have eq1579 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq81
  have eq1820 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq200 x y
       grind)
    | exact superpose eq200 eq14
    | (have j1 := eq200 x y
       grind)
    | exact resolve eq14 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1840 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq200 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq5615 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1840 (τ X1) (τ X0)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq1840
    | (have j0 := eq1840 (τ X1) (τ X0)
       grind)
    | exact resolve eq1840 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq5643 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5615 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5615
    | (have j0 := eq5615 X0 X1
       grind)
    | exact resolve eq5615 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5615
  have eq5651 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5643 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5643
    | (have j0 := eq5643 X0 X1
       grind)
    | exact resolve eq5643 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5643
  have eq5654 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5651 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5651
    | (have j0 := eq5651 X0 X1
       grind)
    | exact resolve eq5651 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5651
  have eq5655 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5654 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5654
    | (have j0 := eq5654 X0 X1
       grind)
    | exact resolve eq5654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5654
  have eq9697 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq244 x y
       grind)
    | exact superpose eq244 eq14
    | (have j1 := eq244 x y
       grind)
    | exact resolve eq14 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq9733 : y = (k y x) := by
    first
    | (have j1 := eq726 x y
       grind)
    | (have r₁ := eq9697
       have r₂ := eq726 x y
       grind)
    | exact resolve eq9697 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq9697
  have eq9897 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23 x y
       have i₂ := eq9733
       grind)
    | exact superpose eq9733 eq23
    | (have j0 := eq23 x y
       grind)
    | exact resolve eq23 eq9733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq9900 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq780 x y
       have i₂ := eq9733
       grind)
    | exact superpose eq9733 eq780
    | (have j0 := eq780 x y
       grind)
    | exact resolve eq780 eq9733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9901 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1840 x y
       have i₂ := eq9733
       grind)
    | exact superpose eq9733 eq1840
    | (have j0 := eq1840 x y
       grind)
    | exact resolve eq1840 eq9733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9903 : x ≠ y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5655 y x
       have i₂ := eq9733
       grind)
    | exact superpose eq9733 eq5655
    | (have j0 := eq5655 y x
       grind)
    | exact resolve eq5655 eq9733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9733
  have eq11343 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 y x
       have i₂ := eq9897
       grind)
    | exact superpose eq9897 eq8
    | exact resolve eq8 eq9897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14135 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11343
       have i₂ := eq9897
       grind)
    | exact superpose eq9897 eq11343
    | exact resolve eq11343 eq9897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9897 eq11343
  have eq14151 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14135
       have r₂ := eq9903
       grind)
    | exact resolve eq14135 eq9903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9903 eq14135
  have eq14726 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq58 y y
       have i₂ := eq14151
       grind)
    | exact superpose eq14151 eq58
    | (have j0 := eq58 y y
       grind)
    | (have r₁ := eq58 y y
       have r₂ := eq14151
       grind)
    | exact resolve eq58 eq14151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq14151
  have eq14735 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq14726
  have eq14970 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1840 y y
       have i₂ := eq14735
       grind)
    | exact superpose eq14735 eq1840
    | (have j0 := eq1840 y y
       grind)
    | exact resolve eq1840 eq14735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14735
  have eq14974 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14970
  have eq18200 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1820
       have i₂ := eq654 x y
       grind)
    | exact superpose eq654 eq1820
    | (have j1 := eq654 x y
       grind)
    | (have r₁ := eq1820
       have r₂ := eq654 x y
       grind)
    | exact resolve eq1820 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq18202 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1820
       have i₂ := eq780 x y
       grind)
    | exact superpose eq780 eq1820
    | (have j1 := eq780 (σ x) (σ y)
       grind)
    | (have r₁ := eq1820
       have r₂ := eq780 x y
       grind)
    | exact resolve eq1820 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780 eq1820
  have eq18207 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18202
  have eq18209 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq18200
  have eq18390 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq18209
       grind)
    | exact superpose eq18209 eq14
    | exact resolve eq14 eq18209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18209
  have eq18985 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq18207
       grind)
    | exact superpose eq18207 eq14
    | exact resolve eq14 eq18207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18996 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88 (σ x) y
       have i₂ := eq18207
       grind)
    | exact superpose eq18207 eq88
    | (have j0 := eq88 (σ x) y
       grind)
    | exact resolve eq88 eq18207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq18207
  have eq19019 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18996
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq18996
    | exact resolve eq18996 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18996
  have eq19036 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq5655 y x
       grind)
    | (have r₁ := eq19019
       have r₂ := eq5655 y x
       grind)
    | exact resolve eq19019 eq5655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19019
  have eq19167 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18985
       have i₂ := eq9900
       grind)
    | exact superpose eq9900 eq18985
    | exact resolve eq18985 eq9900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9900 eq18985
  have eq19170 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq19167
  have eq19739 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14974
       have i₂ := eq19036
       grind)
    | exact superpose eq19036 eq14974
    | exact resolve eq14974 eq19036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14974 eq19036
  have eq19811 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq19739
  have eq19838 : x = (M.op x y) := by
    first
    | (have r₁ := eq19811
       have r₂ := eq19170
       grind)
    | exact resolve eq19811 eq19170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19170 eq19811
  have eq20287 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18390
       have i₂ := eq19838
       grind)
    | exact superpose eq19838 eq18390
    | exact resolve eq18390 eq19838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18390
  have eq20288 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq8 y x
       have i₂ := eq19838
       grind)
    | exact superpose eq19838 eq8
    | exact resolve eq8 eq19838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20303 : x = (M.op y y) := by grind
  clear eq20287
  have eq20433 : x = (k y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1579 y
       have i₂ := eq20303
       grind)
    | exact superpose eq20303 eq1579
    | exact resolve eq1579 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1579
  have eq20438 : y = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq20303
       grind)
    | exact superpose eq20303 eq8
    | exact resolve eq8 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21689 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1066 y
       have i₂ := eq20433
       grind)
    | exact superpose eq20433 eq1066
    | exact resolve eq1066 eq20433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066 eq20433
  have eq21723 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq21689
       have r₂ := eq9901
       grind)
    | exact resolve eq21689 eq9901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9901 eq21689
  have eq29800 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21723
       grind)
    | exact superpose eq21723 eq14
    | exact resolve eq14 eq21723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21723
  have eq29848 : (σ x) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq29800
       have i₂ := eq19838
       grind)
    | exact superpose eq19838 eq29800
    | exact resolve eq29800 eq19838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19838 eq29800
  have eq29849 : x = (k x x) := by grind
  clear eq29848
  have eq30503 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1840 x x
       have i₂ := eq29849
       grind)
    | exact superpose eq29849 eq1840
    | (have j0 := eq1840 x x
       grind)
    | exact resolve eq1840 eq29849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840
  have eq30505 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5655 x x
       have i₂ := eq29849
       grind)
    | exact superpose eq29849 eq5655
    | (have j0 := eq5655 x x
       grind)
    | (have r₁ := eq5655 x x
       have r₂ := eq29849
       grind)
    | exact resolve eq5655 eq29849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5655 eq29849
  have eq30506 : x = (M.op x x) := by grind
  clear eq30505
  have eq30507 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq30503
  have eq31247 : y = (M.op y x) := by
    first
    | (have i₁ := eq20288
       have i₂ := eq30506
       grind)
    | exact superpose eq30506 eq20288
    | exact resolve eq20288 eq30506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20288
  have eq31988 : y = (M.op y y) := by
    first
    | (have i₁ := eq20438
       have i₂ := eq31247
       grind)
    | exact superpose eq31247 eq20438
    | exact resolve eq20438 eq31247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20438 eq31247
  have eq32020 : x = y := by
    first
    | (have i₁ := eq31988
       have i₂ := eq20303
       grind)
    | exact superpose eq20303 eq31988
    | exact resolve eq31988 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20303 eq31988
  have eq32167 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq32020
       grind)
    | exact superpose eq32020 eq14
    | exact resolve eq14 eq32020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32020
  have eq32236 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq32167
       have i₂ := eq30506
       grind)
    | exact superpose eq30506 eq32167
    | exact resolve eq32167 eq30506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30506 eq32167
  have eq32237 : False := by grind
  exact eq32237

/-- `Equation58`: `x = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation58 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law58 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law58.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq83 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq83 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq83 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq83 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq87 (σ X0) (σ X1)
       grind)
    | exact superpose eq87 eq13
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0 X1
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq103
    | exact resolve eq103 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq103
  have eq1869 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq108 x y
       grind)
    | exact superpose eq108 eq14
    | (have r₁ := eq14
       have r₂ := eq108 x y
       grind)
    | exact resolve eq14 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq1892 : False := by grind
  exact eq1892

/-- `Equation72`: `x = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pxx_pxy_Equation72 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law72 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law72.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8 X0 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq15 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op X0 X0) X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11
    | (have j0 := eq11 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq11 (M.op X0 X0) X0
       have r₂ := eq15 X0
       grind)
    | exact resolve eq11 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq24 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq14
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq18 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq18
    | exact resolve eq18 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq25 (M.op X0 X0)
       have i₂ := eq18 X0
       grind)
    | exact superpose eq18 eq25
    | exact resolve eq25 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op (M.op X0 X0) (M.op X0 X0)) X1
       have i₂ := eq18 X0
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq18 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq18 X0
       grind)
    | exact superpose eq18 eq11
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq281 : ∀ X0 : G, (k (M.op X0 X0) X0) ≠ X0 ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq280
    | (have j0 := eq280 X0
       grind)
    | exact resolve eq280 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq286 : ∀ X0 : G, (M.op X0 (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq275
    | exact resolve eq275 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq288 : ∀ X0 : G, (k (k (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq272 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq272
    | exact resolve eq272 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq292 : ∀ X0 : G, (k (M.op X0 X0) X0) ≠ X0 ∨ (k (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq281
    | (have j0 := eq281 X0
       grind)
    | exact resolve eq281 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq363 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq67
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq67 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq364 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq363
  have eq811 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (M.op X0 X0) X0) X1
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq8
    | exact resolve eq8 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq844 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq274 X1 X2
       have i₂ := eq274 X1 X0
       grind)
    | exact superpose eq274 eq274
    | exact resolve eq274 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X1 X1) X2
       have i₂ := eq274 X1 X0
       grind)
    | exact superpose eq274 eq8
    | exact resolve eq8 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq942 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq286 X1
       have i₂ := eq811 X1 X0
       grind)
    | exact superpose eq811 eq286
    | exact resolve eq286 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq811
  have eq2091 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq862 (σ x) (σ y) X0
       have i₂ := eq364
       grind)
    | exact superpose eq364 eq862
    | exact resolve eq862 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq2109 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq862 X1 X2 X1
       have i₂ := eq844 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq862 X1 X2 X1
       have i₂ := eq844 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq844 eq862
    | exact resolve eq862 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq862
  have eq2257 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2091 x
       have i₂ := eq8 (σ x) x
       grind)
    | exact superpose eq8 eq2091
    | exact resolve eq2091 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq3616 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35 y y
       have i₂ := eq2257
       grind)
    | exact superpose eq2257 eq35
    | exact resolve eq35 eq2257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3648 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ y)
       have i₂ := eq2257
       grind)
    | exact superpose eq2257 eq11
    | (have r₁ := eq11 x y
       have r₂ := eq2257
       grind)
    | exact resolve eq11 eq2257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2257
  have eq3664 : (σ x) = (σ (k y y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3648
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq3648
    | exact resolve eq3648 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3648
  have eq3683 : (σ x) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3664
       have r₂ := eq3616
       grind)
    | exact resolve eq3664 eq3616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3616 eq3664
  have eq3814 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq3683
       grind)
    | exact superpose eq3683 eq9
    | exact resolve eq9 eq3683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3683
  have eq3858 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3814
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq3814
    | exact resolve eq3814 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3814
  have eq6508 : ∀ X0 : G, (M.op X0 X0) ≠ (k (k (M.op X0 X0) X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (k (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq292 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq292
    | exact resolve eq292 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq292
  have eq6530 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (k (k (M.op X0 X0) X0) (M.op X0 X0)) (k (k (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6508 X0
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq6508
    | (have j0 := eq6508 X0
       grind)
    | exact resolve eq6508 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6508
  have eq6541 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq6530 X0
       have i₂ := eq288 X0
       grind)
    | exact superpose eq288 eq6530
    | (have j0 := eq6530 X0
       grind)
    | exact resolve eq6530 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq6530
  have eq6549 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6541 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq6541 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq6541 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6541
  have eq6596 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq6549 (σ X0)
       grind)
    | exact superpose eq6549 eq13
    | exact resolve eq13 eq6549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6629 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3858
       have i₂ := eq6549 y
       grind)
    | exact superpose eq6549 eq3858
    | exact resolve eq3858 eq6549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3858
  have eq6660 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6596 X0
       have i₂ := eq6549 X0
       grind)
    | exact superpose eq6549 eq6596
    | exact resolve eq6596 eq6549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6549 eq6596
  have eq7318 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq6660 X0
       grind)
    | exact superpose eq6660 eq8
    | exact resolve eq8 eq6660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6660
  have eq7692 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq6629
       grind)
    | exact superpose eq6629 eq15
    | exact resolve eq15 eq6629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq6629
  have eq7738 : x = (M.op x y) := by grind
  clear eq7692
  have eq7863 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq2109 X0 x y
       have i₂ := eq7738
       grind)
    | exact superpose eq7738 eq2109
    | exact resolve eq2109 eq7738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2109
  have eq7865 : x = (M.op y y) := by
    first
    | (have i₁ := eq7863 x
       have i₂ := eq942 x x
       grind)
    | exact superpose eq942 eq7863
    | exact resolve eq7863 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7863
  have eq17159 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq7318 y X0
       have i₂ := eq7865
       grind)
    | exact superpose eq7865 eq7318
    | exact resolve eq7318 eq7865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7318 eq7865
  have eq17623 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq942 x (σ x)
       have i₂ := eq17159 x
       grind)
    | exact superpose eq17159 eq942
    | exact resolve eq942 eq17159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942 eq17159
  have eq18082 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17623
       grind)
    | exact superpose eq17623 eq14
    | exact resolve eq14 eq17623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17623
  have eq18108 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq18082
       have i₂ := eq7738
       grind)
    | exact superpose eq7738 eq18082
    | exact resolve eq18082 eq7738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7738 eq18082
  have eq18109 : False := by grind
  exact eq18109

/-- `Equation103`: `x = x ◇ ((x ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation103 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law103 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law103.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq49 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq337 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq336 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq343 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq337 (σ X0) (σ X1)
       grind)
    | exact superpose eq337 eq13
    | exact resolve eq13 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq343 X0 X1
       have i₂ := eq337 X0 X1
       grind)
    | exact superpose eq337 eq343
    | exact resolve eq343 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq343
  have eq1766 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq356 x y
       grind)
    | exact superpose eq356 eq14
    | (have r₁ := eq14
       have r₂ := eq356 x y
       grind)
    | exact resolve eq14 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq1786 : False := by grind
  exact eq1786
