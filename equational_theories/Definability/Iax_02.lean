import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation307`: `x ◇ x = x ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation307 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law307 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law307.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
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
  have eq19 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq23 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19
    | exact resolve eq19 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq26 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0
       have i₂ := eq12 X0 X1
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
  have eq27 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq31 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq36 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  clear eq26
  have eq49 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq22
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq66 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq23 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq23
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq107 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq36
  have eq124 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq107 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq107
    | exact resolve eq107 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq137 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq28 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq28
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq14
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq538 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq601 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq538
    | (have j0 := eq538 X0 X1
       grind)
    | exact resolve eq538 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq659 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq1180 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq55 x y
       grind)
    | exact superpose eq55 eq14
    | (have j1 := eq55 x y
       grind)
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1187 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8 (σ x)
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq8
    | (have j1 := eq55 X0 X0
       grind)
    | exact resolve eq8 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1405 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq149
       have i₂ := eq659 y x
       grind)
    | exact superpose eq659 eq149
    | (have j1 := eq659 y x
       grind)
    | (have r₁ := eq149
       have r₂ := eq659 y x
       grind)
    | exact resolve eq149 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq1407 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq149
       have i₂ := eq601 y x
       grind)
    | exact superpose eq601 eq149
    | (have j1 := eq601 (σ y) (σ x)
       grind)
    | (have r₁ := eq149
       have r₂ := eq601 y x
       grind)
    | exact resolve eq149 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq1408 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1407
  have eq1410 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq1405
  have eq1422 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq124 x
       have i₂ := eq1408
       grind)
    | exact superpose eq1408 eq124
    | exact resolve eq124 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1425 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 (σ x)
       have i₂ := eq1408
       grind)
    | exact superpose eq1408 eq8
    | exact resolve eq8 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1430 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1422
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1422
    | exact resolve eq1422 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq1510 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq601 y x
       have i₂ := eq1430
       grind)
    | exact superpose eq1430 eq601
    | (have j0 := eq601 y x
       grind)
    | exact resolve eq601 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601 eq1430
  have eq1512 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq1510
  have eq1550 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq14
    | (have j1 := eq43 x y
       grind)
    | exact resolve eq14 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1561 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1714 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq137
    | (have j0 := eq137 X1 (τ X0)
       grind)
    | exact resolve eq137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq1821 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1714 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1714
    | (have j0 := eq1714 X0 X1
       grind)
    | exact resolve eq1714 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1714
  have eq1831 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1821 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1821
    | (have j0 := eq1821 X0 X1
       grind)
    | exact resolve eq1821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821
  have eq4217 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq124 x
       have i₂ := eq1410
       grind)
    | exact superpose eq1410 eq124
    | exact resolve eq124 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq1410
  have eq4231 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq4217
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4217
    | exact resolve eq4217 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4217
  have eq4232 : x = (k x y) := by grind
  clear eq4231
  have eq5754 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1425
       grind)
    | exact superpose eq1425 eq14
    | exact resolve eq14 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq6256 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5754
       have i₂ := eq1512
       grind)
    | exact superpose eq1512 eq5754
    | exact resolve eq5754 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512 eq5754
  have eq6257 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq6256
  have eq8431 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq66
    | (have j0 := eq66 X1 (σ X0)
       grind)
    | exact resolve eq66 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq8532 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8431 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq8431
    | (have j0 := eq8431 X0 X1
       grind)
    | exact resolve eq8431 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8431
  have eq9840 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1561 x y
       have i₂ := eq4232
       grind)
    | exact superpose eq4232 eq1561
    | (have j0 := eq1561 x y
       grind)
    | exact resolve eq1561 eq4232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561 eq4232
  have eq10463 : (τ (σ y)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq49 (σ x) x
       have i₂ := eq1408
       grind)
    | exact superpose eq1408 eq49
    | exact resolve eq49 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1408
  have eq10821 : (τ (σ y)) = (k (τ (σ x)) x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10463
       have r₂ := eq6257
       grind)
    | exact resolve eq10463 eq6257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10463
  have eq10864 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10821
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq10821
    | exact resolve eq10821 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10821
  have eq10871 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10864
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq10864
    | exact resolve eq10864 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10864
  have eq10903 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8532 x x
       have i₂ := eq10871
       grind)
    | exact superpose eq10871 eq8532
    | exact resolve eq8532 eq10871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8532 eq10871
  have eq10905 : (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq10903
  have eq10916 : y = (M.op x x) := by
    first
    | (have r₁ := eq10905
       have r₂ := eq6257
       grind)
    | exact resolve eq10905 eq6257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6257 eq10905
  have eq11098 : y = (M.op x y) := by
    first
    | (have i₁ := eq8 x
       have i₂ := eq10916
       grind)
    | exact superpose eq10916 eq8
    | exact resolve eq8 eq10916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11102 : x ≠ y ∨ x = (k x x) := by
    first
    | (have i₁ := eq61 x x
       have i₂ := eq10916
       grind)
    | exact superpose eq10916 eq61
    | (have j0 := eq61 x x
       grind)
    | exact resolve eq61 eq10916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq11626 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1180
       have i₂ := eq1831 x y
       grind)
    | exact superpose eq1831 eq1180
    | (have j1 := eq1831 x y
       grind)
    | (have r₁ := eq1180
       have r₂ := eq1831 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1180
       have r₂ := eq1831 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1180 eq1831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180 eq1831
  have eq11635 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) ∨ x = y := by grind
  clear eq11626
  have eq11643 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11635
       have i₂ := eq11098
       grind)
    | exact superpose eq11098 eq11635
    | exact resolve eq11635 eq11098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11635
  have eq14240 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1187 x
       have i₂ := eq11643
       grind)
    | exact superpose eq11643 eq1187
    | exact resolve eq1187 eq11643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187 eq11643
  have eq14296 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14240
  have eq14307 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq14296
       have r₂ := eq9840
       grind)
    | exact resolve eq14296 eq9840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9840 eq14296
  have eq14356 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq14307
       grind)
    | exact superpose eq14307 eq14
    | exact resolve eq14 eq14307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14307
  have eq14382 : (σ y) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14356
       have i₂ := eq11098
       grind)
    | exact superpose eq11098 eq14356
    | exact resolve eq14356 eq11098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11098 eq14356
  have eq14383 : x = y := by grind
  clear eq14382
  have eq14780 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq14383
       grind)
    | exact superpose eq14383 eq14
    | exact resolve eq14 eq14383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14788 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1550
       have i₂ := eq14383
       grind)
    | exact superpose eq14383 eq1550
    | exact resolve eq1550 eq14383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550
  have eq14806 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq11102
       have i₂ := eq14383
       grind)
    | exact superpose eq14383 eq11102
    | (have r₁ := eq11102
       have r₂ := eq14383
       grind)
    | exact resolve eq11102 eq14383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11102
  have eq14807 : x = (k x x) := by grind
  clear eq14806
  have eq14816 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14788
       have i₂ := eq10916
       grind)
    | exact superpose eq10916 eq14788
    | exact resolve eq14788 eq10916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14788
  have eq14819 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14780
       have i₂ := eq10916
       grind)
    | exact superpose eq10916 eq14780
    | exact resolve eq14780 eq10916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10916 eq14780
  have eq14820 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14816
       have i₂ := eq14807
       grind)
    | exact superpose eq14807 eq14816
    | exact resolve eq14816 eq14807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14807 eq14816
  have eq14823 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14819
       have i₂ := eq14383
       grind)
    | exact superpose eq14383 eq14819
    | exact resolve eq14819 eq14383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14819
  have eq14824 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14820
       have i₂ := eq14383
       grind)
    | exact superpose eq14383 eq14820
    | exact resolve eq14820 eq14383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14383 eq14820
  have eq14825 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq14824
  have eq14828 : False := by grind
  exact eq14828

/-- `Equation309`: `x ◇ x = x ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation309 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law309 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law309.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X0)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq27 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
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
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq52 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq23
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq28 (σ X1) (σ X0)
       grind)
    | exact superpose eq28 eq13
    | (have j1 := eq28 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq67 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq97 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq37
  have eq112 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq97
    | exact resolve eq97 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq151 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq29 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq29
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29 x y
       grind)
    | exact superpose eq29 eq14
    | (have j1 := eq29 x y
       grind)
    | exact resolve eq14 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq29 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq572 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq10
    | (have j1 := eq32 X0 X1
       grind)
    | exact resolve eq10 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq641 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq572 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq572
    | (have j0 := eq572 X0 X1
       grind)
    | exact resolve eq572 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq1079 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq40 X0 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq40 X0 X0
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1089 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X1) (σ X0)
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq8
    | (have j1 := eq40 X0 X1
       grind)
    | exact resolve eq8 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1422 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq163
       have i₂ := eq641 y x
       grind)
    | exact superpose eq641 eq163
    | (have j1 := eq641 (σ y) (σ x)
       grind)
    | (have r₁ := eq163
       have r₂ := eq641 y x
       grind)
    | exact resolve eq163 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq1423 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1422
  have eq1437 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq112 x
       have i₂ := eq1423
       grind)
    | exact superpose eq1423 eq112
    | exact resolve eq112 eq1423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1446 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 (σ x) (σ x)
       have i₂ := eq1423
       grind)
    | exact superpose eq1423 eq8
    | exact resolve eq8 eq1423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1449 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1437
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1437
    | exact resolve eq1437 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437
  have eq1529 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq641 y x
       have i₂ := eq1449
       grind)
    | exact superpose eq1449 eq641
    | (have j0 := eq641 y x
       grind)
    | exact resolve eq641 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq1449
  have eq1531 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq1529
  have eq1569 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq63 x y
       grind)
    | exact superpose eq63 eq14
    | (have j1 := eq63 x y
       grind)
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1585 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4098 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1446
       grind)
    | exact superpose eq1446 eq14
    | exact resolve eq14 eq1446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq4433 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4098
       have i₂ := eq1531
       grind)
    | exact superpose eq1531 eq4098
    | exact resolve eq4098 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1531 eq4098
  have eq4434 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq4433
  have eq10518 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq67
    | (have j0 := eq67 X1 (σ X0)
       grind)
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10544 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq184 (τ X0)
       have i₂ := eq67 (τ X0) X0
       grind)
    | exact superpose eq67 eq184
    | (have j0 := eq184 (τ X0)
       have j1 := eq67 (τ X0) X0
       grind)
    | exact resolve eq184 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq184
  have eq10609 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10544 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10544
    | (have j0 := eq10544 X0
       grind)
    | exact resolve eq10544 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10544
  have eq10625 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10518 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq10518
    | (have j0 := eq10518 X0 X1
       grind)
    | exact resolve eq10518 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10518
  have eq10645 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10609 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10609
    | (have j0 := eq10609 X0
       grind)
    | exact resolve eq10609 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10609
  have eq10670 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq10645 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10645
    | (have j0 := eq10645 X0
       grind)
    | exact resolve eq10645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10645
  have eq10688 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10670 X0
       have j1 := eq45 X0 X0
       grind)
    | (have r₁ := eq10670 x
       have r₂ := eq45 x x
       grind)
    | exact resolve eq10670 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq10670
  have eq10705 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10688 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq10688
    | (have j0 := eq10688 (σ X0)
       grind)
    | exact resolve eq10688 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10688
  have eq10744 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10705 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq10705
    | (have j0 := eq10705 X0
       grind)
    | exact resolve eq10705 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10705
  have eq12873 : (τ (σ y)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq52 (σ x) x
       have i₂ := eq1423
       grind)
    | exact superpose eq1423 eq52
    | exact resolve eq52 eq1423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1423
  have eq13293 : (τ (σ y)) = (k (τ (σ x)) x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12873
       have r₂ := eq4434
       grind)
    | exact resolve eq12873 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12873
  have eq13339 : (k x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13293
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq13293
    | exact resolve eq13293 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13293
  have eq13348 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13339
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq13339
    | exact resolve eq13339 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13339
  have eq13385 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10625 x x
       have i₂ := eq13348
       grind)
    | exact superpose eq13348 eq10625
    | exact resolve eq10625 eq13348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13348
  have eq13387 : (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq13385
  have eq13398 : y = (M.op x x) := by
    first
    | (have r₁ := eq13387
       have r₂ := eq4434
       grind)
    | exact resolve eq13387 eq4434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4434 eq13387
  have eq13585 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq10744 x
       have i₂ := eq13398
       grind)
    | exact superpose eq13398 eq10744
    | (have j0 := eq10744 x
       grind)
    | exact resolve eq10744 eq13398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10744
  have eq13586 : y = (M.op x y) := by
    first
    | (have i₁ := eq8 x x
       have i₂ := eq13398
       grind)
    | exact superpose eq13398 eq8
    | exact resolve eq8 eq13398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13892 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq613 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq13893 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq13892 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13892
    | (have j0 := eq13892 X0
       grind)
    | exact resolve eq13892 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13892
  have eq16613 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq13893 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq13893
    | (have j0 := eq13893 (σ X0)
       grind)
    | exact resolve eq13893 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13893
  have eq16628 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16613 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq16613
    | (have j0 := eq16613 X0
       grind)
    | exact resolve eq16613 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16613
  have eq26331 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq16628 X0
       have i₂ := eq10625 X0 X0
       grind)
    | exact superpose eq10625 eq16628
    | (have j0 := eq16628 X0
       have j1 := eq10625 X0 X0
       grind)
    | (have r₁ := eq16628 x
       have r₂ := eq10625 x x
       grind)
    | exact resolve eq16628 eq10625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10625 eq16628
  have eq26360 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq26331 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26331
  have eq27077 : y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26360 x
       have i₂ := eq13398
       grind)
    | exact superpose eq13398 eq26360
    | exact resolve eq26360 eq13398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13398 eq26360
  have eq28782 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1089 x x
       have i₂ := eq27077
       grind)
    | exact superpose eq27077 eq1089
    | exact resolve eq1089 eq27077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089 eq27077
  have eq28880 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq28782
  have eq57597 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1079 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq57598 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq57597 X0 X1
       have j1 := eq151 X1 X0
       grind)
    | (have r₁ := eq57597 (k X1 X1) X0
       have r₂ := eq151 X0 X1
       grind)
    | (have r₁ := eq57597 X0 (σ (k X1 X1))
       have r₂ := eq151 (σ X0) X1
       grind)
    | (have r₁ := eq57597 X1 X0
       have r₂ := eq151 X0 X1
       grind)
    | exact resolve eq57597 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq57597
  have eq57789 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X1)
       have i₂ := eq57598 (τ X1) X0
       grind)
    | (have i₁ := eq17 X0 X1
       have i₂ := eq57598 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq57598 eq17
    | (have j1 := eq57598 (τ X1) X0
       grind)
    | exact resolve eq17 eq57598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq57598
  have eq57875 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57789 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq57789
    | (have j0 := eq57789 X0 X1
       grind)
    | exact resolve eq57789 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57789
  have eq57889 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57875 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq57875
    | (have j0 := eq57875 X0 X1
       grind)
    | exact resolve eq57875 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57875
  have eq58109 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1569
       have i₂ := eq57889 y x
       grind)
    | exact superpose eq57889 eq1569
    | (have j1 := eq57889 y x
       grind)
    | exact resolve eq1569 eq57889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569 eq57889
  have eq58238 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by grind
  clear eq58109
  have eq58321 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq58238
       grind)
    | exact superpose eq58238 eq14
    | exact resolve eq14 eq58238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58238
  have eq58366 : (σ y) ≠ (σ y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq58321
       have i₂ := eq13586
       grind)
    | exact superpose eq13586 eq58321
    | exact resolve eq58321 eq13586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58321
  have eq58367 : y = (k x x) := by grind
  clear eq58366
  have eq58487 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1585 x x
       have i₂ := eq58367
       grind)
    | exact superpose eq58367 eq1585
    | (have j0 := eq1585 x x
       grind)
    | exact resolve eq1585 eq58367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585
  have eq98328 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq28880
       grind)
    | exact superpose eq28880 eq14
    | exact resolve eq14 eq28880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28880
  have eq98347 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq98328
       have i₂ := eq13586
       grind)
    | exact superpose eq13586 eq98328
    | exact resolve eq98328 eq13586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98328
  have eq99782 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq98347
       have i₂ := eq40 x x
       grind)
    | exact superpose eq40 eq98347
    | (have j1 := eq40 x x
       grind)
    | exact resolve eq98347 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq99783 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq98347
       have i₂ := eq63 x x
       grind)
    | exact superpose eq63 eq98347
    | (have j1 := eq63 x x
       grind)
    | exact resolve eq98347 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq98347
  have eq99797 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq99783
       have r₂ := eq58487
       grind)
    | exact resolve eq99783 eq58487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58487 eq99783
  have eq99798 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have r₁ := eq99782
       have r₂ := eq13585
       grind)
    | exact resolve eq99782 eq13585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13585 eq99782
  have eq99804 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq99797
       have i₂ := eq58367
       grind)
    | exact superpose eq58367 eq99797
    | exact resolve eq99797 eq58367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99797
  have eq99805 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq99804
  have eq99806 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq99798
       have i₂ := eq58367
       grind)
    | exact superpose eq58367 eq99798
    | exact resolve eq99798 eq58367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99798
  have eq99807 : (σ x) = (σ (k x x)) := by grind
  clear eq99806
  have eq99811 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq99807
       have i₂ := eq58367
       grind)
    | exact superpose eq58367 eq99807
    | exact resolve eq99807 eq58367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58367 eq99807
  have eq101887 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq99811
       grind)
    | exact superpose eq99811 eq14
    | exact resolve eq14 eq99811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102154 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq101887
       have i₂ := eq99805
       grind)
    | exact superpose eq99805 eq101887
    | exact resolve eq101887 eq99805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99805 eq101887
  have eq102175 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq102154
       have i₂ := eq13586
       grind)
    | exact superpose eq13586 eq102154
    | exact resolve eq102154 eq13586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13586 eq102154
  have eq102194 : False := by grind
  exact eq102194

/-- `Equation310`: `x ◇ x = x ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation310 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law310 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law310.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 X1)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2
       have i₂ := eq8 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X1 X1) X1
       have i₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X0
       have i₂ := eq8 X0 X1
       grind)
    | (have i₁ := eq8 X0 (M.op X1 X1)
       have i₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X1 X1))) = X0 := by
    intro X0 X1
    grind
  have eq22 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 (M.op X1 X0)
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
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
  have eq31 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq36 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq41 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq43 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq36
    | exact resolve eq36 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq45 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq23
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41
    | exact resolve eq41 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq96 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq43 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq43
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq146 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq50
  have eq163 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq146 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq146
    | exact resolve eq146 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq166 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq31
    | exact resolve eq31 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 (M.op X1 X1)
       have i₂ := eq8 X0 X1
       grind)
    | (have i₁ := eq175 X0 X0
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq175
    | (have j0 := eq175 X0 X0
       grind)
    | exact resolve eq175 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq29 (σ y) (σ x) X0
       grind)
    | exact superpose eq29 eq14
    | (have j1 := eq29 (σ y) x X0
       grind)
    | exact resolve eq14 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq299 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq163 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq163 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq163
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq163 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq34 x y
       grind)
    | exact superpose eq34 eq14
    | (have j1 := eq34 x y
       grind)
    | exact resolve eq14 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq8
    | (have j1 := eq34 X0 X0
       grind)
    | exact resolve eq8 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq9
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ X0)) ∨ (σ (k X3 X0)) = (M.op (σ X3) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X2 (σ X3)
       have i₂ := eq34 X3 X0
       grind)
    | exact superpose eq34 eq16
    | (have j1 := eq34 X3 X0
       grind)
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ X0)) = X3 ∨ (k X1 X3) = (M.op X1 X3) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30 X3 X1 (σ X2)
       have i₂ := eq34 X2 X0
       grind)
    | exact superpose eq34 eq30
    | (have j0 := eq30 X3 X1 X2
       have j1 := eq34 X2 X0
       grind)
    | exact resolve eq30 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq465 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq2626 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq465 (τ X0)
       have i₂ := eq23 X0 (τ X0)
       grind)
    | exact superpose eq23 eq465
    | (have j0 := eq465 (τ X0)
       grind)
    | exact resolve eq465 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2628 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2626 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2626
    | (have j0 := eq2626 X0
       grind)
    | exact resolve eq2626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2626
  have eq2631 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2628 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2628
    | (have j0 := eq2628 X0
       grind)
    | exact resolve eq2628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2628
  have eq2643 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2631 (τ X0)
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq2631
    | (have j0 := eq2631 (τ X0)
       grind)
    | exact resolve eq2631 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq2631
  have eq2678 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq45
    | exact resolve eq45 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2786 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq10
    | (have j1 := eq45 X0 X1
       grind)
    | exact resolve eq10 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq2822 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2678 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2678
    | (have j0 := eq2678 X0 X1
       grind)
    | exact resolve eq2678 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2678
  have eq2914 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq4729 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ X0)
       have i₂ := eq166 X0 X0
       grind)
    | exact superpose eq166 eq8
    | (have j1 := eq166 X0 X0
       grind)
    | exact resolve eq8 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq5376 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq96
    | (have j0 := eq96 X1 (σ X0)
       grind)
    | exact resolve eq96 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq5465 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5376 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq5376
    | (have j0 := eq5376 X0 X1
       grind)
    | exact resolve eq5376 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5376
  have eq5523 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq425
       have i₂ := eq2914 y x
       grind)
    | exact superpose eq2914 eq425
    | (have j1 := eq2914 y x
       grind)
    | (have r₁ := eq425
       have r₂ := eq2914 y x
       grind)
    | exact resolve eq425 eq2914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2914
  have eq5524 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq425
       have i₂ := eq2822 y x
       grind)
    | exact superpose eq2822 eq425
    | (have j1 := eq2822 (σ y) (σ x)
       grind)
    | (have r₁ := eq425
       have r₂ := eq2822 y x
       grind)
    | exact resolve eq425 eq2822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq5525 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq5524
  have eq5526 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq5523
  have eq6161 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq163 x
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq163
    | exact resolve eq163 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6164 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ x)
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq8
    | exact resolve eq8 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6169 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X1 (σ y))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (σ x) X0
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq17
    | exact resolve eq17 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq6206 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6161
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6161
    | exact resolve eq6161 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6161
  have eq6579 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6206
       grind)
    | exact superpose eq6206 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq6206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6583 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2822 y x
       have i₂ := eq6206
       grind)
    | exact superpose eq6206 eq2822
    | (have j0 := eq2822 y x
       grind)
    | exact resolve eq2822 eq6206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822 eq6206
  have eq6584 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq6583
  have eq6585 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq6579
  have eq8105 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq163 x
       have i₂ := eq5526
       grind)
    | exact superpose eq5526 eq163
    | exact resolve eq163 eq5526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq5526
  have eq8155 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq8105
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq8105
    | exact resolve eq8105 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8105
  have eq8156 : x = (k x y) := by grind
  clear eq8155
  have eq9481 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq441 x x
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq441
    | exact resolve eq441 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq9546 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9481
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq9481
    | exact resolve eq9481 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9481
  have eq11531 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (M.op X1 X1)) = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 (τ X0)
       have i₂ := eq427 (τ X0) X1
       grind)
    | exact superpose eq427 eq23
    | (have j1 := eq427 (τ X0) X1
       grind)
    | exact resolve eq23 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq427
  have eq11666 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq11531 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11531
    | (have j0 := eq11531 X0 X1
       grind)
    | exact resolve eq11531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11531
  have eq11693 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11666 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11666
    | (have j0 := eq11666 X0 X1
       grind)
    | exact resolve eq11666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11666
  have eq13991 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq457 y X0 X1 x
       grind)
    | exact superpose eq457 eq14
    | (have j1 := eq457 y X0 X1 x
       grind)
    | exact resolve eq14 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq14093 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13991 X0 X1
       have i₂ := eq8156
       grind)
    | exact superpose eq8156 eq13991
    | (have j0 := eq13991 X0 X1
       grind)
    | exact resolve eq13991 eq8156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13991
  have eq15967 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 (M.op X1 X1)
       have i₂ := eq11693 X0 X1
       grind)
    | exact superpose eq11693 eq175
    | (have j0 := eq175 X0 (M.op X1 X1)
       have j1 := eq11693 X0 X1
       grind)
    | (have r₁ := eq175 X0 X0
       have r₂ := eq11693 X0 X1
       grind)
    | exact resolve eq175 eq11693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11693
  have eq16082 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15967 X0 X1
       have j1 := eq185 X0 X1
       grind)
    | (have r₁ := eq15967 (M.op X1 X1) X1
       have r₂ := eq185 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq15967 X0 X1
       have r₂ := eq185 X0 X1
       grind)
    | exact resolve eq15967 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq15967
  have eq24532 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14
       have i₂ := eq463 y X0 x X1
       grind)
    | exact superpose eq463 eq14
    | (have j1 := eq463 y X0 x X1
       grind)
    | (have r₁ := eq14
       have r₂ := eq463 y (σ x) x (σ (M.op x y))
       grind)
    | exact resolve eq14 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq24660 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 (σ y)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24532 X0 X1
       have i₂ := eq8156
       grind)
    | exact superpose eq8156 eq24532
    | (have j0 := eq24532 X0 X1
       grind)
    | exact resolve eq24532 eq8156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24532
  have eq46085 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq2786 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786
  have eq46086 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq46085 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46085
    | (have j0 := eq46085 X0
       grind)
    | exact resolve eq46085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46085
  have eq46213 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq46086 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq46086
    | (have j0 := eq46086 X0
       have j1 := eq31 X0 X0
       grind)
    | (have r₁ := eq46086 X0
       have r₂ := eq31 X0 X0
       grind)
    | exact resolve eq46086 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46242 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq46086 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq46086
    | (have j0 := eq46086 (σ X0)
       grind)
    | exact resolve eq46086 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46249 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46242 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46242
    | (have j0 := eq46242 X0
       grind)
    | exact resolve eq46242 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46242
  have eq46254 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq46213 X0
       have j1 := eq46086 X0
       grind)
    | (have r₁ := eq46213 X0
       have r₂ := eq46086 X0
       grind)
    | exact resolve eq46213 eq46086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46086 eq46213
  have eq50877 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq46249 X0
       have i₂ := eq5465 X0 X0
       grind)
    | exact superpose eq5465 eq46249
    | (have j0 := eq46249 X0
       have j1 := eq5465 X0 X0
       grind)
    | (have r₁ := eq46249 x
       have r₂ := eq5465 x x
       grind)
    | exact resolve eq46249 eq5465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5465 eq46249
  have eq50895 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq50877 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50877
  have eq65868 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2643 (σ X0)
       have i₂ := eq299 (σ X0) X0
       grind)
    | exact superpose eq299 eq2643
    | (have j0 := eq2643 (σ X0)
       have j1 := eq299 (σ X0) X0
       grind)
    | exact resolve eq2643 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299 eq2643
  have eq65905 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq65868 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq65868
    | (have j0 := eq65868 X0
       grind)
    | exact resolve eq65868 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65868
  have eq65917 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq65905 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq65905
    | (have j0 := eq65905 X0
       grind)
    | exact resolve eq65905 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65905
  have eq65921 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq65917 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq65917
    | (have j0 := eq65917 X0
       grind)
    | exact resolve eq65917 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65917
  have eq65924 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq65921 X0
       have j1 := eq175 X0 X0
       grind)
    | (have r₁ := eq65921 x
       have r₂ := eq175 x x
       grind)
    | exact resolve eq65921 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq65921
  have eq66663 : x ≠ (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq65924 x
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq65924
    | (have j0 := eq65924 x
       grind)
    | exact resolve eq65924 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65924
  have eq66736 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66663
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq66663
    | exact resolve eq66663 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66663
  have eq81580 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq9546
       grind)
    | exact superpose eq9546 eq9
    | exact resolve eq9 eq9546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9546
  have eq81590 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq81580
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq81580
    | exact resolve eq81580 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81580
  have eq81934 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq31 x x
       have i₂ := eq81590
       grind)
    | exact superpose eq81590 eq31
    | exact resolve eq31 eq81590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq81590
  have eq81947 : y = (M.op x x) ∨ x = y := by grind
  clear eq81934
  have eq81968 : ∀ X0 : G, (k X0 (M.op X0 y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq81947
       grind)
    | exact superpose eq81947 eq18
    | exact resolve eq18 eq81947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq81947
  have eq82589 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq81968 x
       have i₂ := eq6585
       grind)
    | exact superpose eq6585 eq81968
    | exact resolve eq81968 eq6585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6585 eq81968
  have eq82645 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq82589
       have r₂ := eq66736
       grind)
    | exact resolve eq82589 eq66736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66736 eq82589
  have eq82810 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq465 x
       have i₂ := eq82645
       grind)
    | exact superpose eq82645 eq465
    | (have j0 := eq465 x
       grind)
    | exact resolve eq465 eq82645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq82831 : ∀ X0 : G, x ≠ x ∨ x = (k x (M.op X0 X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16082 x X0
       have i₂ := eq82645
       grind)
    | exact superpose eq82645 eq16082
    | (have j0 := eq16082 x X0
       grind)
    | (have r₁ := eq16082 x x
       have r₂ := eq82645
       grind)
    | exact resolve eq16082 eq82645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16082 eq82645
  have eq82863 : ∀ X0 : G, x = (k x (M.op X0 X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq82831 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82831
  have eq82868 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq82810
  have eq85789 : x = (k x (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82863 (σ x)
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq82863
    | exact resolve eq82863 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82863
  have eq85807 : x = (k x (σ y)) ∨ y = (M.op x x) := by grind
  clear eq85789
  have eq88190 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq219 X0
       have i₂ := eq82868
       grind)
    | exact superpose eq82868 eq219
    | (have j0 := eq219 X0
       grind)
    | exact resolve eq219 eq82868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq88191 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5525
       have i₂ := eq82868
       grind)
    | exact superpose eq82868 eq5525
    | exact resolve eq5525 eq82868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5525
  have eq88300 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq88191
  have eq88314 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq88190 X0
       grind)
    | (have r₁ := eq88190 X0
       have r₂ := eq6584
       grind)
    | exact resolve eq88190 eq6584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88190
  have eq88604 : (σ x) = (σ y) ∨ y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50895 x
       have i₂ := eq88300
       grind)
    | exact superpose eq88300 eq50895
    | exact resolve eq50895 eq88300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50895 eq88300
  have eq88622 : y = (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq88604
  have eq88936 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq4729 x x
       have i₂ := eq88622
       grind)
    | exact superpose eq88622 eq4729
    | exact resolve eq4729 eq88622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4729 eq88622
  have eq88984 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq88936 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88936
  have eq90564 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1
       have i₂ := eq88984 X0
       grind)
    | (have i₁ := eq8 (σ y) X1
       have i₂ := eq88984 (σ y)
       grind)
    | exact superpose eq88984 eq8
    | exact resolve eq8 eq88984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90566 : ∀ X0 X1 : G, (M.op X0 (σ y)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq88984 X0
       grind)
    | (have i₁ := eq12 (σ y) X1
       have i₂ := eq88984 (σ y)
       grind)
    | exact superpose eq88984 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq88984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88984
  have eq99113 : x = (M.op x (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85807
       have i₂ := eq88314 x
       grind)
    | exact superpose eq88314 eq85807
    | exact resolve eq85807 eq88314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85807 eq88314
  have eq99127 : x = (M.op x (σ y)) ∨ y = (M.op x x) := by grind
  clear eq99113
  have eq99139 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6169 X0 x
       have i₂ := eq99127
       grind)
    | exact superpose eq99127 eq6169
    | exact resolve eq6169 eq99127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6169 eq99127
  have eq99173 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq99139 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99139
  have eq99479 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq6164 X0
       have i₂ := eq99173 X0
       grind)
    | (have i₁ := eq6164 x
       have i₂ := eq99173 x
       grind)
    | exact superpose eq99173 eq6164
    | exact resolve eq6164 eq99173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6164
  have eq99658 : (σ x) = (M.op (σ x) x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82868
       have i₂ := eq99173 (σ x)
       grind)
    | exact superpose eq99173 eq82868
    | exact resolve eq82868 eq99173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82868 eq99173
  have eq99758 : (σ x) = (M.op (σ x) x) ∨ y = (M.op x x) := by grind
  clear eq99658
  have eq99781 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq99479 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99479
  have eq103177 : (σ (M.op x y)) ≠ (M.op (σ x) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq99781 (σ x)
       grind)
    | exact superpose eq99781 eq14
    | exact resolve eq14 eq99781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99781
  have eq108456 : (σ x) ≠ (M.op (σ x) x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103177
       have i₂ := eq6584
       grind)
    | exact superpose eq6584 eq103177
    | exact resolve eq103177 eq6584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6584 eq103177
  have eq108457 : (σ x) ≠ (M.op (σ x) x) ∨ y = (M.op x x) := by grind
  clear eq108456
  have eq108459 : y = (M.op x x) := by
    first
    | (have r₁ := eq108457
       have r₂ := eq99758
       grind)
    | exact resolve eq108457 eq99758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99758 eq108457
  have eq108499 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq108459
       grind)
    | exact superpose eq108459 eq8
    | exact resolve eq8 eq108459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108502 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq108459
       grind)
    | exact superpose eq108459 eq16
    | exact resolve eq16 eq108459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq109054 : ∀ X0 : G, (M.op X0 y) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq46254 X0
       have i₂ := eq108499 X0
       grind)
    | (have i₁ := eq46254 y
       have i₂ := eq108499 y
       grind)
    | exact superpose eq108499 eq46254
    | (have j0 := eq46254 X0
       grind)
    | exact resolve eq46254 eq108499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46254
  have eq109469 : ∀ X0 X1 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14093 X0 X1
       have i₂ := eq108499 x
       grind)
    | exact superpose eq108499 eq14093
    | (have j0 := eq14093 X0 X1
       grind)
    | exact resolve eq14093 eq108499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14093
  have eq109472 : ∀ X0 X1 : G, (σ x) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ y)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24660 X0 X1
       have i₂ := eq108499 x
       grind)
    | exact superpose eq108499 eq24660
    | (have j0 := eq24660 X0 X1
       grind)
    | exact resolve eq24660 eq108499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24660
  have eq109479 : ∀ X0 X1 : G, (σ x) ≠ (σ y) ∨ (M.op X0 (σ y)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq109472 X0 X1
       have i₂ := eq108459
       grind)
    | exact superpose eq108459 eq109472
    | (have j0 := eq109472 X0 X1
       grind)
    | exact resolve eq109472 eq108459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109472
  have eq109482 : ∀ X0 X1 : G, (σ x) ≠ (σ y) ∨ (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq109469 X0 X1
       have i₂ := eq108459
       grind)
    | exact superpose eq108459 eq109469
    | (have j0 := eq109469 X0 X1
       grind)
    | exact resolve eq109469 eq108459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109469
  have eq109524 : ∀ X0 : G, (M.op X0 y) ≠ X0 ∨ (σ (M.op (τ X0) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq109054 X0
       have i₂ := eq108499 (τ X0)
       grind)
    | exact superpose eq108499 eq109054
    | (have j0 := eq109054 X0
       grind)
    | exact resolve eq109054 eq108499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109054
  have eq109578 : ∀ X0 X1 : G, (M.op X0 (σ y)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq109479 X0 X1
       have j1 := eq90566 X0 X1
       grind)
    | (have r₁ := eq109479 X0 X1
       have r₂ := eq90566 X0 X1
       grind)
    | exact resolve eq109479 eq90566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90566 eq109479
  have eq109579 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq109482 X0 X1
       have j1 := eq90564 X0 X1
       grind)
    | (have r₁ := eq109482 X0 X1
       have r₂ := eq90564 X0 X1
       grind)
    | exact resolve eq109482 eq90564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90564 eq109482
  have eq109597 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq109579 X0 x
       have i₂ := eq108502 X0 x
       grind)
    | exact superpose eq108502 eq109579
    | exact resolve eq109579 eq108502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108502 eq109579
  have eq109993 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq109597 (σ x)
       grind)
    | exact superpose eq109597 eq14
    | exact resolve eq14 eq109597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110020 : (σ (M.op x x)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq109993
       have i₂ := eq108499 x
       grind)
    | exact superpose eq108499 eq109993
    | exact resolve eq109993 eq108499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109993
  have eq110051 : (σ y) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq110020
       have i₂ := eq108459
       grind)
    | exact superpose eq108459 eq110020
    | exact resolve eq110020 eq108459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110020
  have eq127358 : ∀ X0 : G, (σ (M.op x y)) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq109578 (σ x) X0
       grind)
    | (have i₁ := eq14
       have i₂ := eq109578 X0 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq109578 eq14
    | (have j1 := eq109578 (σ x) X0
       grind)
    | (have r₁ := eq14
       have r₂ := eq109578 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq109578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109578
  have eq127438 : ∀ X0 : G, (σ (M.op x x)) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq127358 X0
       have i₂ := eq108499 x
       grind)
    | exact superpose eq108499 eq127358
    | (have j0 := eq127358 X0
       grind)
    | exact resolve eq127358 eq108499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127358
  have eq127452 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq127438 X0
       have i₂ := eq108459
       grind)
    | exact superpose eq108459 eq127438
    | (have j0 := eq127438 X0
       grind)
    | exact resolve eq127438 eq108459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127438
  have eq127675 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have j0 := eq127452 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127452
  have eq127676 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq127675
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq127675
    | exact resolve eq127675 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127675
  have eq127677 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq127676
       have i₂ := eq8156
       grind)
    | exact superpose eq8156 eq127676
    | exact resolve eq127676 eq8156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8156 eq127676
  have eq127678 : (σ x) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq127677
       have i₂ := eq109597 (σ x)
       grind)
    | exact superpose eq109597 eq127677
    | exact resolve eq127677 eq109597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109597 eq127677
  have eq127769 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq110051
       have i₂ := eq127678
       grind)
    | exact superpose eq127678 eq110051
    | exact resolve eq110051 eq127678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110051
  have eq127875 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op (τ (σ x)) y)) := by
    first
    | (have i₁ := eq109524 (σ x)
       have i₂ := eq127678
       grind)
    | exact superpose eq127678 eq109524
    | (have j0 := eq109524 (σ x)
       grind)
    | (have r₁ := eq109524 (σ x)
       have r₂ := eq127678
       grind)
    | exact resolve eq109524 eq127678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109524 eq127678
  have eq127909 : (σ x) = (σ (M.op (τ (σ x)) y)) := by grind
  clear eq127875
  have eq127928 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq127909
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq127909
    | exact resolve eq127909 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127909
  have eq128013 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq127928
       have i₂ := eq108499 x
       grind)
    | exact superpose eq108499 eq127928
    | exact resolve eq127928 eq108499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108499 eq127928
  have eq128032 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq128013
       have i₂ := eq108459
       grind)
    | exact superpose eq108459 eq128013
    | exact resolve eq128013 eq108459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108459 eq128013
  have eq128037 : False := by grind
  exact eq128037

/-- `Equation313`: `x ◇ x = y ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation313 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law313 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law313.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X1)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X1 X0))) = X1 := by
    intro X0 X1
    grind
  have eq25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq51 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq108 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (M.op X0 X0) X1
       have i₂ := eq18 X0 X0
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq142 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq51
  have eq159 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq142 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq142
    | exact resolve eq142 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq171 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq447 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq459 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ (k X0 X1)) (M.op (σ X0) (σ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (σ X0) (σ X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq18
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq491 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq6428 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq491 (M.op X0 X0)
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq491
    | (have j0 := eq491 (M.op X0 X0)
       grind)
    | exact resolve eq491 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6434 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq6428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6428
  have eq14542 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq447
       have i₂ := eq33 y x
       grind)
    | exact superpose eq33 eq447
    | (have j1 := eq33 y x
       grind)
    | exact resolve eq447 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq447
       have i₂ := eq108 y x
       grind)
    | exact superpose eq108 eq447
    | (have j1 := eq108 y x
       grind)
    | exact resolve eq447 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq14550 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq14543
  have eq14551 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq14542
  have eq14588 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq131 (σ x)
       have i₂ := eq14550
       grind)
    | exact superpose eq14550 eq131
    | exact resolve eq131 eq14550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq14550
  have eq14688 : (σ y) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14588
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq14588
    | exact resolve eq14588 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14588
  have eq16939 : (k y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq14688
       grind)
    | exact superpose eq14688 eq9
    | exact resolve eq9 eq14688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14688
  have eq16984 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16939
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq16939
    | exact resolve eq16939 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16939
  have eq16985 : y = (k y y) := by
    first
    | (have j1 := eq171 y y
       grind)
    | (have r₁ := eq16984
       have r₂ := eq171 y y
       grind)
    | exact resolve eq16984 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16984
  have eq17478 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq491 y
       have i₂ := eq16985
       grind)
    | exact superpose eq16985 eq491
    | (have j0 := eq491 y
       grind)
    | exact resolve eq491 eq16985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq17486 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq108 y y
       have i₂ := eq16985
       grind)
    | exact superpose eq16985 eq108
    | (have j0 := eq108 y x
       grind)
    | exact resolve eq108 eq16985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq16985
  have eq17488 : y = (M.op y y) := by grind
  clear eq17486
  have eq17492 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq17478
  have eq17710 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq117 y x
       have i₂ := eq17488
       grind)
    | exact superpose eq17488 eq117
    | exact resolve eq117 eq17488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq19158 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (M.op y (σ (M.op X0 X0))) y) := by
    intro X0
    first
    | (have i₁ := eq6434 X0
       have i₂ := eq17710 (σ (M.op X0 X0))
       grind)
    | exact superpose eq17710 eq6434
    | exact resolve eq6434 eq17710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6434
  have eq46401 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq47010 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (M.op (M.op y (σ (M.op X0 X0))) y) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46401 X0
       have i₂ := eq17710 (σ (M.op X0 X0))
       grind)
    | exact superpose eq17710 eq46401
    | (have j0 := eq46401 X0
       grind)
    | exact resolve eq46401 eq17710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17710 eq46401
  have eq47188 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47010 X0
       have i₂ := eq19158 X0
       grind)
    | exact superpose eq19158 eq47010
    | (have j0 := eq47010 X0
       grind)
    | exact resolve eq47010 eq19158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19158 eq47010
  have eq47279 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47188 X0
       have i₂ := eq8 (σ X0) (σ X0)
       grind)
    | exact superpose eq8 eq47188
    | (have j0 := eq47188 X0
       grind)
    | exact resolve eq47188 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47188
  have eq47280 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq47279 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47279
  have eq47584 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8 (σ X0) (σ X0)
       have i₂ := eq47280 X0
       grind)
    | exact superpose eq47280 eq8
    | exact resolve eq8 eq47280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83496 : x = (k x (τ (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq159 x
       have i₂ := eq14551
       grind)
    | exact superpose eq14551 eq159
    | exact resolve eq159 eq14551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq14551
  have eq83725 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq83496
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq83496
    | exact resolve eq83496 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83496
  have eq83779 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33 y x
       have i₂ := eq83725
       grind)
    | exact superpose eq83725 eq33
    | (have j0 := eq33 y x
       grind)
    | exact resolve eq33 eq83725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq83725
  have eq83791 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq83779
  have eq84289 : x = (k x (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19 y x
       have i₂ := eq83791
       grind)
    | exact superpose eq83791 eq19
    | exact resolve eq19 eq83791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq83791
  have eq84384 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84289
       have i₂ := eq17488
       grind)
    | exact superpose eq17488 eq84289
    | exact resolve eq84289 eq17488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17488 eq84289
  have eq84407 : x = (k x y) := by
    first
    | (have j1 := eq171 x y
       grind)
    | (have r₁ := eq84384
       have r₂ := eq171 x y
       grind)
    | exact resolve eq84384 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq84384
  have eq85343 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq459 x y
       have i₂ := eq84407
       grind)
    | exact superpose eq84407 eq459
    | (have j0 := eq459 x y
       grind)
    | exact resolve eq459 eq84407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459 eq84407
  have eq85352 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq85343
       have i₂ := eq17492
       grind)
    | exact superpose eq17492 eq85343
    | exact resolve eq85343 eq17492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17492 eq85343
  have eq85358 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq85352
       have i₂ := eq8 (σ x) (σ x)
       grind)
    | exact superpose eq8 eq85352
    | exact resolve eq85352 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85352
  have eq85359 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq85358
  have eq85363 : (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq85359
       have i₂ := eq47280 x
       grind)
    | exact superpose eq47280 eq85359
    | exact resolve eq85359 eq47280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47280 eq85359
  have eq85744 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq85363
       grind)
    | exact superpose eq85363 eq9
    | exact resolve eq9 eq85363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85923 : y = (M.op x x) := by
    first
    | (have i₁ := eq85744
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq85744
    | exact resolve eq85744 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85744
  have eq86436 : y = (M.op x y) := by
    first
    | (have i₁ := eq8 x x
       have i₂ := eq85923
       grind)
    | exact superpose eq85923 eq8
    | exact resolve eq8 eq85923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85923
  have eq116337 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq47584 x
       have i₂ := eq85363
       grind)
    | exact superpose eq85363 eq47584
    | exact resolve eq47584 eq85363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47584 eq85363
  have eq116756 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq116337
       grind)
    | exact superpose eq116337 eq14
    | exact resolve eq14 eq116337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116337
  have eq116950 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq116756
       have i₂ := eq86436
       grind)
    | exact superpose eq86436 eq116756
    | exact resolve eq116756 eq86436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86436 eq116756
  have eq116951 : False := by grind
  exact eq116951

/-- `Equation315`: `x ◇ x = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation315 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law315 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law315.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X0)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    grind
  have eq21 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq33 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
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
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq46 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq25
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq119 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq51
  have eq137 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq119
    | exact resolve eq119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq440 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq446 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X1) (σ X0)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq8
    | (have j1 := eq35 X0 X1
       grind)
    | exact resolve eq8 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq538 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq21 X0 X0
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq568 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq538 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq538
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq538 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1233 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq568 X0 X1
       grind)
    | exact superpose eq568 eq33
    | (have j0 := eq33 X0 X1
       have j1 := eq568 X0 X1
       grind)
    | exact resolve eq33 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq568
  have eq1248 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1233 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq4835 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46
    | exact resolve eq46 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq4984 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4835 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq4835
    | (have j0 := eq4835 X0 X1
       grind)
    | exact resolve eq4835 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4835
  have eq10579 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq440
       have i₂ := eq4984 y x
       grind)
    | exact superpose eq4984 eq440
    | (have j1 := eq4984 (σ y) (σ x)
       grind)
    | (have r₁ := eq440
       have r₂ := eq4984 y x
       grind)
    | exact resolve eq440 eq4984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq4984
  have eq10580 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq10579
  have eq10598 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq137 x
       have i₂ := eq10580
       grind)
    | exact superpose eq10580 eq137
    | exact resolve eq137 eq10580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq10613 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq538 (σ x)
       have i₂ := eq10580
       grind)
    | exact superpose eq10580 eq538
    | exact resolve eq538 eq10580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10580
  have eq10684 : (σ y) = (σ (k y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10613
       have i₂ := eq13 y y
       grind)
    | exact superpose eq13 eq10613
    | exact resolve eq10613 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10613
  have eq10689 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10598
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq10598
    | exact resolve eq10598 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10598
  have eq10791 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq10689
       grind)
    | exact superpose eq10689 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq10689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10689
  have eq10800 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq10791
  have eq10938 : (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 y x
       have i₂ := eq10800
       grind)
    | exact superpose eq10800 eq8
    | exact resolve eq8 eq10800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10800
  have eq12351 : (k y y) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq10684
       grind)
    | exact superpose eq10684 eq9
    | exact resolve eq9 eq10684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10684
  have eq12389 : y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12351
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq12351
    | exact resolve eq12351 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12351
  have eq12690 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1248 y y
       have i₂ := eq12389
       grind)
    | exact superpose eq12389 eq1248
    | (have j0 := eq1248 y x
       grind)
    | exact resolve eq1248 eq12389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248 eq12389
  have eq12693 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq12690
  have eq13991 : y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12693
       have i₂ := eq10938
       grind)
    | exact superpose eq10938 eq12693
    | exact resolve eq12693 eq10938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10938 eq12693
  have eq14050 : y = (M.op x x) := by grind
  clear eq13991
  have eq14657 : x = (k x y) := by grind
  have eq14665 : y = (k y y) := by
    first
    | (have i₁ := eq538 x
       have i₂ := eq14050
       grind)
    | exact superpose eq14050 eq538
    | exact resolve eq538 eq14050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq14674 : y = (M.op x y) := by
    first
    | (have i₁ := eq8 x x
       have i₂ := eq14050
       grind)
    | exact superpose eq14050 eq8
    | exact resolve eq8 eq14050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14050
  have eq15753 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq479 y
       have i₂ := eq14665
       grind)
    | exact superpose eq14665 eq479
    | (have j0 := eq479 y
       grind)
    | exact resolve eq479 eq14665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq14665
  have eq15770 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq15753
  have eq18352 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq446 x y
       have i₂ := eq14657
       grind)
    | exact superpose eq14657 eq446
    | (have j0 := eq446 x y
       grind)
    | exact resolve eq446 eq14657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq14657
  have eq18566 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18352
       have i₂ := eq15770
       grind)
    | exact superpose eq15770 eq18352
    | exact resolve eq18352 eq15770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15770 eq18352
  have eq18567 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq18566
  have eq20801 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8 (σ x) (σ x)
       have i₂ := eq18567
       grind)
    | exact superpose eq18567 eq8
    | exact resolve eq8 eq18567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18567
  have eq21454 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq20801
       grind)
    | exact superpose eq20801 eq14
    | exact resolve eq14 eq20801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20801
  have eq21554 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq21454
       have i₂ := eq14674
       grind)
    | exact superpose eq14674 eq21454
    | exact resolve eq21454 eq14674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14674 eq21454
  have eq21555 : False := by grind
  exact eq21555

/-- `Equation323`: `x ◇ y = x ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation323 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law323 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law323.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq27 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq27 (τ X1) X0
       grind)
    | exact superpose eq27 eq18
    | (have j1 := eq27 (τ X1) X0
       grind)
    | exact resolve eq18 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq28 (σ X1) (σ X0)
       grind)
    | exact superpose eq28 eq13
    | (have j1 := eq28 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq37
  have eq123 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq106
    | exact resolve eq106 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq136 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq29 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq29
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29 x y
       grind)
    | exact superpose eq29 eq14
    | (have j1 := eq29 x y
       grind)
    | exact resolve eq14 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) (σ X1)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X0 X1
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq175 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (M.op X0 X1)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq504 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq564 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq504 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq504
    | (have j0 := eq504 X0 X1
       grind)
    | exact resolve eq504 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq619 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq658 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq619 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq619
    | (have j0 := eq619 X0 X1
       grind)
    | exact resolve eq619 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq1028 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) (σ X1)
       have i₂ := eq40 X0 X1
       grind)
    | exact superpose eq40 eq8
    | (have j1 := eq40 X0 X1
       grind)
    | exact resolve eq8 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1358 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq148
       have i₂ := eq658 y x
       grind)
    | exact superpose eq658 eq148
    | (have j1 := eq658 y x
       grind)
    | (have r₁ := eq148
       have r₂ := eq658 y x
       grind)
    | exact resolve eq148 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq1359 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq148
       have i₂ := eq564 y x
       grind)
    | exact superpose eq564 eq148
    | (have j1 := eq564 (σ y) (σ x)
       grind)
    | (have r₁ := eq148
       have r₂ := eq564 y x
       grind)
    | exact resolve eq148 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq1360 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1359
  have eq1361 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq1358
  have eq1374 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq123 x
       have i₂ := eq1360
       grind)
    | exact superpose eq1360 eq123
    | exact resolve eq123 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1380 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 (σ x) (σ x)
       have i₂ := eq1360
       grind)
    | exact superpose eq1360 eq8
    | exact resolve eq8 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1384 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1374
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1374
    | exact resolve eq1374 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq1460 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1384
       grind)
    | exact superpose eq1384 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1464 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq564 y x
       have i₂ := eq1384
       grind)
    | exact superpose eq1384 eq564
    | (have j0 := eq564 y x
       grind)
    | exact resolve eq564 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq1384
  have eq1466 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq1464
  have eq1467 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1460
  have eq1516 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1526 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq175 x y
       have i₂ := eq1467
       grind)
    | exact superpose eq1467 eq175
    | (have r₁ := eq175 x y
       have r₂ := eq1467
       grind)
    | exact resolve eq175 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq1467
  have eq1530 : x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq1526
  have eq1636 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq136
    | (have j0 := eq136 X1 (τ X0)
       grind)
    | exact resolve eq136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq1738 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1636 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1636
    | (have j0 := eq1636 X0 X1
       grind)
    | exact resolve eq1636 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1636
  have eq1748 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1738 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1738
    | (have j0 := eq1738 X0 X1
       grind)
    | exact resolve eq1738 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738
  have eq1994 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq151 x x
       have i₂ := eq1530
       grind)
    | exact superpose eq1530 eq151
    | (have j0 := eq151 x x
       grind)
    | exact resolve eq151 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq1530
  have eq1997 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1994
  have eq3649 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq123 x
       have i₂ := eq1361
       grind)
    | exact superpose eq1361 eq123
    | exact resolve eq123 eq1361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq1361
  have eq3659 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3649
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3649
    | exact resolve eq3649 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3649
  have eq3660 : x = (k x y) := by grind
  clear eq3659
  have eq4075 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq3660
       grind)
    | exact superpose eq3660 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq3660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4518 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq4075
  have eq7150 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1380
       grind)
    | exact superpose eq1380 eq14
    | exact resolve eq14 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380
  have eq7772 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7150
       have i₂ := eq1466
       grind)
    | exact superpose eq1466 eq7150
    | exact resolve eq7150 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466 eq7150
  have eq7773 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq7772
  have eq8885 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1360
       have i₂ := eq1997
       grind)
    | exact superpose eq1997 eq1360
    | exact resolve eq1360 eq1997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360 eq1997
  have eq8910 : (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq8885
  have eq8924 : y = (M.op x x) := by
    first
    | (have r₁ := eq8910
       have r₂ := eq7773
       grind)
    | exact resolve eq8910 eq7773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7773 eq8910
  have eq9069 : y = (M.op x y) := by
    first
    | (have i₁ := eq8 x x
       have i₂ := eq8924
       grind)
    | exact superpose eq8924 eq8
    | exact resolve eq8 eq8924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9100 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1516 x y
       have i₂ := eq3660
       grind)
    | exact superpose eq3660 eq1516
    | (have j0 := eq1516 x y
       grind)
    | exact resolve eq1516 eq3660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516
  have eq9482 : x = (M.op x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq3660
       have i₂ := eq1748 x y
       grind)
    | exact superpose eq1748 eq3660
    | (have j1 := eq1748 x y
       grind)
    | exact resolve eq3660 eq1748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748 eq3660
  have eq9585 : x = (M.op x y) ∨ y = (k x x) := by
    first
    | (have r₁ := eq9482
       have r₂ := eq4518
       grind)
    | exact resolve eq9482 eq4518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4518 eq9482
  have eq9621 : y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq9585
       have i₂ := eq9069
       grind)
    | exact superpose eq9069 eq9585
    | exact resolve eq9585 eq9069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9585
  have eq15395 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1028 x x
       have i₂ := eq9621
       grind)
    | exact superpose eq9621 eq1028
    | exact resolve eq1028 eq9621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028 eq9621
  have eq15468 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq15395
       have r₂ := eq9100
       grind)
    | exact resolve eq15395 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15395
  have eq15496 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq15468
       grind)
    | exact superpose eq15468 eq14
    | exact resolve eq14 eq15468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15468
  have eq15525 : (σ y) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15496
       have i₂ := eq9069
       grind)
    | exact superpose eq9069 eq15496
    | exact resolve eq15496 eq9069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9069 eq15496
  have eq15526 : x = y := by grind
  clear eq15525
  have eq15925 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq15526
       grind)
    | exact superpose eq15526 eq14
    | exact resolve eq14 eq15526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15950 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9100
       have i₂ := eq15526
       grind)
    | exact superpose eq15526 eq9100
    | exact resolve eq9100 eq15526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9100
  have eq15953 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq15950
  have eq15965 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15925
       have i₂ := eq8924
       grind)
    | exact superpose eq8924 eq15925
    | exact resolve eq15925 eq8924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8924 eq15925
  have eq15966 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq15965
       have i₂ := eq15953
       grind)
    | exact superpose eq15953 eq15965
    | exact resolve eq15965 eq15953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15953 eq15965
  have eq15967 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq15966
       have i₂ := eq15526
       grind)
    | exact superpose eq15526 eq15966
    | exact resolve eq15966 eq15526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15526 eq15966
  have eq15968 : False := by grind
  exact eq15968

/-- `Equation325`: `x ◇ y = x ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation325 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law325 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law325.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X0)) := by
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
  have eq16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 X0 X1
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
  have eq29 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq27 (τ X0) X1
       grind)
    | exact superpose eq27 eq18
    | (have j1 := eq27 (τ X0) X1
       grind)
    | exact resolve eq18 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23
    | exact resolve eq23 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 (σ X0) (σ X1)
       grind)
    | exact superpose eq28 eq13
    | (have j1 := eq28 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq102 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq37
  have eq117 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq102
    | exact resolve eq102 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq143 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45 (M.op X1 X0) X0
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq45
    | (have j0 := eq45 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq45 (M.op X0 X0) X0
       have r₂ := eq8 X0 X0
       grind)
    | exact resolve eq45 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq29
    | (have j0 := eq29 X0 X1
       have j1 := eq29 X0 X1
       grind)
    | exact resolve eq29 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq29 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq29
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) (σ X1)
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X1 X0
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (σ X1) (σ X1)
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq16
    | (have j1 := eq29 X0 X1
       grind)
    | exact resolve eq16 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq29 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq117 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq117
    | (have j1 := eq29 X0 X1
       grind)
    | exact resolve eq117 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq244 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq117 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq117 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq117
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq117 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq263 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq243 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq243
    | (have j0 := eq243 X0 X1
       grind)
    | exact resolve eq243 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq650 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq188 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq188
    | (have j0 := eq188 (τ X0)
       grind)
    | exact resolve eq188 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq650 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq650
    | (have j0 := eq650 X0
       grind)
    | exact resolve eq650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq655 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq652 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq652
    | (have j0 := eq652 X0
       grind)
    | exact resolve eq652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq668 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq10
    | (have j1 := eq32 X1 X0
       grind)
    | exact resolve eq10 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq747 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq668 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq668
    | (have j0 := eq668 X0 X1
       grind)
    | exact resolve eq668 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq769 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq655 (τ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq655
    | (have j0 := eq655 (τ X0)
       grind)
    | exact resolve eq655 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq772 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
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
  have eq815 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq772 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq772
    | (have j0 := eq772 X0 X1
       grind)
    | exact resolve eq772 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq1203 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq40 y x
       grind)
    | exact superpose eq40 eq14
    | (have j1 := eq40 y x
       grind)
    | exact resolve eq14 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq40 X0 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq40 X0 X0
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1873 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq40
    | (have j0 := eq40 X1 X0
       have j1 := eq62 X0 X1
       grind)
    | exact resolve eq40 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq62
  have eq1887 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1873 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873
  have eq2498 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq66
    | (have j0 := eq66 X1 (σ X0)
       grind)
    | exact resolve eq66 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2517 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq188 (τ X0)
       have i₂ := eq66 (τ X0) X0
       grind)
    | exact superpose eq66 eq188
    | (have j0 := eq188 (τ X0)
       have j1 := eq66 (τ X0) X0
       grind)
    | exact resolve eq188 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq2558 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2517 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2517
    | (have j0 := eq2517 X0
       grind)
    | exact resolve eq2517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2517
  have eq2569 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2498 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2498
    | (have j0 := eq2498 X0 X1
       grind)
    | exact resolve eq2498 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2498
  have eq2582 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 (σ (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2558 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2558
    | (have j0 := eq2558 X0
       grind)
    | exact resolve eq2558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558
  have eq2598 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq2582 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2582
    | (have j0 := eq2582 X0
       grind)
    | exact resolve eq2582 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2582
  have eq2611 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2598 X0
       have j1 := eq45 X0 X0
       grind)
    | (have r₁ := eq2598 X0
       have r₂ := eq45 X0 X0
       grind)
    | exact resolve eq2598 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598
  have eq2626 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq155 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq155
    | (have j0 := eq155 X1 (τ X0)
       grind)
    | exact resolve eq155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2752 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2626 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2626
    | (have j0 := eq2626 X0 X1
       grind)
    | exact resolve eq2626 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2626
  have eq2763 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2752 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2752
    | (have j0 := eq2752 X0 X1
       grind)
    | exact resolve eq2752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752
  have eq2777 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2611 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2611
    | (have j0 := eq2611 (σ X0)
       grind)
    | exact resolve eq2611 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2611
  have eq2803 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2777 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq2777
    | (have j0 := eq2777 X0
       grind)
    | exact resolve eq2777 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2777
  have eq3015 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq188 X0
       have i₂ := eq2569 X0 X0
       grind)
    | exact superpose eq2569 eq188
    | (have j0 := eq188 X0
       have j1 := eq2569 X0 X0
       grind)
    | (have r₁ := eq188 x
       have r₂ := eq2569 x x
       grind)
    | exact resolve eq188 eq2569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3051 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3015 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3015
  have eq3098 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq3114 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq172 (τ X0) (τ X1)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq172
    | (have j0 := eq172 (τ X0) (τ X1)
       grind)
    | exact resolve eq172 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq3146 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3114 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3114
    | (have j0 := eq3114 X0 X1
       grind)
    | exact resolve eq3114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3114
  have eq3153 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (M.op X0 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3146 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3146
    | (have j0 := eq3146 X0 X1
       grind)
    | exact resolve eq3146 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3146
  have eq3155 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3153 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3153
    | (have j0 := eq3153 X0 X1
       grind)
    | exact resolve eq3153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3153
  have eq3156 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X0 X1) = (M.op X0 (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3155 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3155
    | (have j0 := eq3155 X0 X1
       grind)
    | exact resolve eq3155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3155
  have eq3157 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3156 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3156
    | (have j0 := eq3156 X0 X1
       grind)
    | exact resolve eq3156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq3346 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3347 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq3923 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq154 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq154 X0 X1
       grind)
    | exact superpose eq154 eq9
    | (have j1 := eq154 X0 X1
       grind)
    | exact resolve eq9 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq3978 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3923 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3923
    | (have j0 := eq3923 X0 X1
       grind)
    | exact resolve eq3923 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3923
  have eq8629 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (τ X0) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq244
    | (have j0 := eq244 X1 (τ X0)
       grind)
    | exact resolve eq244 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8761 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8629 X0 X1
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq8629
    | (have j0 := eq8629 X0 X1
       grind)
    | exact resolve eq8629 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8629
  have eq9800 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq263 x y
       grind)
    | exact superpose eq263 eq14
    | (have j1 := eq263 x y
       grind)
    | exact resolve eq14 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq9848 : y = (k y x) := by
    first
    | (have j1 := eq815 x y
       grind)
    | (have r₁ := eq9800
       have r₂ := eq815 x y
       grind)
    | exact resolve eq9800 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9800
  have eq10496 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq747 x y
       have i₂ := eq9848
       grind)
    | exact superpose eq9848 eq747
    | (have j0 := eq747 x y
       grind)
    | exact resolve eq747 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10498 : (M.op y y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3157 y x
       have i₂ := eq9848
       grind)
    | exact superpose eq9848 eq3157
    | (have j0 := eq3157 y (M.op y x)
       grind)
    | exact resolve eq3157 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3157
  have eq13298 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq143 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq143
    | (have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq143 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq143 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13338 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq143 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq13351 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13298
  have eq14294 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq699 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq14295 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14294 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14294
    | (have j0 := eq14294 X0
       grind)
    | exact resolve eq14294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14294
  have eq14401 : x ≠ (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq10498
  have eq14410 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1203
       have i₂ := eq13351 x y
       grind)
    | exact superpose eq13351 eq1203
    | (have j1 := eq13351 x y
       grind)
    | exact resolve eq1203 eq13351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203 eq13351
  have eq14419 : (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by grind
  clear eq14410
  have eq15771 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq14295 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq14295
    | (have j0 := eq14295 (σ X0)
       grind)
    | exact resolve eq14295 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14295
  have eq15783 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15771 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq15771
    | (have j0 := eq15771 X0
       grind)
    | exact resolve eq15771 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15771
  have eq16154 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1887 x y
       grind)
    | exact superpose eq1887 eq14
    | (have j1 := eq1887 x y
       grind)
    | exact resolve eq14 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887
  have eq16239 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16154
       have i₂ := eq9848
       grind)
    | exact superpose eq9848 eq16154
    | exact resolve eq16154 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16154
  have eq19492 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16239
       have i₂ := eq14419
       grind)
    | exact superpose eq14419 eq16239
    | (have r₁ := eq16239
       have r₂ := eq14419
       grind)
    | exact resolve eq16239 eq14419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14419 eq16239
  have eq19498 : (σ x) = (σ (k x y)) ∨ x = (k x y) := by grind
  clear eq19492
  have eq19842 : (k x y) = (τ (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq9 (k x y)
       have i₂ := eq19498
       grind)
    | exact superpose eq19498 eq9
    | exact resolve eq9 eq19498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19498
  have eq19954 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq19842
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq19842
    | exact resolve eq19842 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19842
  have eq19955 : x = (k x y) := by grind
  clear eq19954
  have eq20068 : y = (k x x) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq2763 x y
       have i₂ := eq19955
       grind)
    | exact superpose eq19955 eq2763
    | (have j0 := eq2763 x y
       grind)
    | exact resolve eq2763 eq19955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763
  have eq25227 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq15783 X0
       have i₂ := eq2569 X0 X0
       grind)
    | exact superpose eq2569 eq15783
    | (have j0 := eq15783 X0
       have j1 := eq2569 X0 X0
       grind)
    | (have r₁ := eq15783 x
       have r₂ := eq2569 x x
       grind)
    | exact resolve eq15783 eq2569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25244 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25227 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25227
  have eq27439 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25244 X1
       have i₂ := eq747 X0 X1
       grind)
    | (have i₁ := eq25244 X0
       have i₂ := eq747 (M.op X0 X0) X1
       grind)
    | exact superpose eq747 eq25244
    | (have j1 := eq747 X0 X1
       grind)
    | exact resolve eq25244 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq25244
  have eq35678 : ∀ X0 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq769 (σ X0)
       have i₂ := eq244 (σ X0) X0
       grind)
    | exact superpose eq244 eq769
    | (have j0 := eq769 (σ X0)
       have j1 := eq244 (σ X0) X0
       grind)
    | exact resolve eq769 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq35691 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq769 X0
       have i₂ := eq8761 X0 X0
       grind)
    | exact superpose eq8761 eq769
    | (have j0 := eq769 X0
       have j1 := eq8761 X0 X0
       grind)
    | (have r₁ := eq769 x
       have r₂ := eq8761 x x
       grind)
    | exact resolve eq769 eq8761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq8761
  have eq35700 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq35691 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35691
  have eq35709 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq35678 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35678
    | (have j0 := eq35678 X0
       grind)
    | exact resolve eq35678 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35678
  have eq35723 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 (τ (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq35709 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35709
    | (have j0 := eq35709 X0
       grind)
    | exact resolve eq35709 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35709
  have eq35730 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq35723 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35723
    | (have j0 := eq35723 X0
       grind)
    | exact resolve eq35723 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35723
  have eq35735 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq35730 X0
       have j1 := eq45 X0 X0
       grind)
    | (have r₁ := eq35730 X0
       have r₂ := eq45 X0 X0
       grind)
    | exact resolve eq35730 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq35730
  have eq41263 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3346 (τ X0) (τ X1)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq3346
    | exact resolve eq3346 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq3346
  have eq41330 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq41263 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41263
    | (have j0 := eq41263 X0 X1
       grind)
    | exact resolve eq41263 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41263
  have eq41358 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq41330 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq41330
    | (have j0 := eq41330 X0 X1
       grind)
    | exact resolve eq41330 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41330
  have eq41372 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41358 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq41358
    | (have j0 := eq41358 X0 X1
       grind)
    | exact resolve eq41358 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41358
  have eq41377 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41372 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq41372
    | (have j0 := eq41372 X0 X1
       grind)
    | exact resolve eq41372 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41372
  have eq41378 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41377 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq41377
    | (have j0 := eq41377 X0 X1
       grind)
    | exact resolve eq41377 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41377
  have eq41401 : x ≠ (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq41378 x y
       have i₂ := eq19955
       grind)
    | exact superpose eq19955 eq41378
    | exact resolve eq41378 eq19955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41378
  have eq41649 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3978 x y
       grind)
    | exact superpose eq3978 eq14
    | (have j1 := eq3978 x y
       grind)
    | exact resolve eq14 eq3978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3978
  have eq41910 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq27439 x y
       grind)
    | (have r₁ := eq41649
       have r₂ := eq27439 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq41649
       have r₂ := eq27439 (k y x) (M.op x y)
       grind)
    | (have r₁ := eq41649
       have r₂ := eq27439 x y
       grind)
    | exact resolve eq41649 eq27439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27439 eq41649
  have eq42131 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2569 y y
       have i₂ := eq41910
       grind)
    | exact superpose eq41910 eq2569
    | exact resolve eq2569 eq41910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2569 eq41910
  have eq42144 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq42131
  have eq42986 : x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq42144
       grind)
    | exact superpose eq42144 eq8
    | exact resolve eq8 eq42144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42144
  have eq59601 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq35700 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35700
    | (have j0 := eq35700 (σ X0)
       grind)
    | exact resolve eq35700 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35700
  have eq59691 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59601 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq59601
    | (have j0 := eq59601 X0
       grind)
    | exact resolve eq59601 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59601
  have eq60038 : ∀ X0 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3347 X0 (M.op X0 X0)
       have i₂ := eq13338 X0
       grind)
    | exact superpose eq13338 eq3347
    | (have j0 := eq3347 X0 (M.op X0 X0)
       grind)
    | exact resolve eq3347 eq13338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3347 eq13338
  have eq60041 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq60038 X0
       have j1 := eq3098 X0
       grind)
    | (have r₁ := eq60038 X0
       have r₂ := eq3098 X0
       grind)
    | exact resolve eq60038 eq3098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3098 eq60038
  have eq65727 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1211 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq65783 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq65727 X0 X1
       have j1 := eq155 X1 X0
       grind)
    | (have r₁ := eq65727 (k X1 X1) X0
       have r₂ := eq155 X0 X1
       grind)
    | (have r₁ := eq65727 X0 (σ (k X1 X1))
       have r₂ := eq155 (σ X0) X1
       grind)
    | (have r₁ := eq65727 X1 X0
       have r₂ := eq155 X0 X1
       grind)
    | exact resolve eq65727 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq65727
  have eq65840 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X1)
       have i₂ := eq65783 (τ X1) X0
       grind)
    | (have i₁ := eq17 X0 X1
       have i₂ := eq65783 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq65783 eq17
    | (have j1 := eq65783 (τ X1) X0
       grind)
    | exact resolve eq17 eq65783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq65841 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq65783 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq65783 X0 (σ X0)
       grind)
    | exact superpose eq65783 eq9
    | (have j1 := eq65783 X1 X0
       grind)
    | exact resolve eq9 eq65783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65783
  have eq65897 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq65840 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq65840
    | (have j0 := eq65840 X0 X1
       grind)
    | exact resolve eq65840 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65840
  have eq65907 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq65897 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq65897
    | (have j0 := eq65897 X0 X1
       grind)
    | exact resolve eq65897 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65897
  have eq66366 : y = (k x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq19955
       have i₂ := eq65907 y x
       grind)
    | exact superpose eq65907 eq19955
    | (have j1 := eq65907 y x
       grind)
    | exact resolve eq19955 eq65907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19955 eq65907
  have eq67288 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq15783 x
       have i₂ := eq66366
       grind)
    | exact superpose eq66366 eq15783
    | (have j0 := eq15783 x
       grind)
    | exact resolve eq15783 eq66366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66366
  have eq67330 : (σ x) = (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq67288
       have r₂ := eq42986
       grind)
    | exact resolve eq67288 eq42986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42986 eq67288
  have eq67572 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2803 x
       have i₂ := eq67330
       grind)
    | exact superpose eq67330 eq2803
    | (have j0 := eq2803 x
       grind)
    | (have r₁ := eq2803 x
       have r₂ := eq67330
       grind)
    | exact resolve eq2803 eq67330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2803 eq67330
  have eq67628 : (σ x) = (σ (k x x)) ∨ x = (M.op y x) := by grind
  clear eq67572
  have eq70277 : (k x x) = (τ (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq67628
       grind)
    | exact superpose eq67628 eq9
    | exact resolve eq9 eq67628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67628
  have eq70356 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq70277
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq70277
    | exact resolve eq70277 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70277
  have eq70411 : x = y ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq20068
       have i₂ := eq70356
       grind)
    | exact superpose eq70356 eq20068
    | exact resolve eq20068 eq70356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20068 eq70356
  have eq70467 : x = (M.op y x) ∨ x = y := by grind
  clear eq70411
  have eq71031 : x ≠ x ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq14401
       have i₂ := eq70467
       grind)
    | exact superpose eq70467 eq14401
    | (have r₁ := eq14401
       have r₂ := eq70467
       grind)
    | exact resolve eq14401 eq70467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14401
  have eq71067 : x = (M.op y y) ∨ x = y := by grind
  clear eq71031
  have eq102445 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq65841 (σ X0) X1
       grind)
    | exact superpose eq65841 eq13
    | (have j1 := eq65841 (σ X0) X1
       grind)
    | exact resolve eq13 eq65841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65841
  have eq102469 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq102445 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq102445
    | (have j0 := eq102445 X0 X1
       grind)
    | exact resolve eq102445 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102445
  have eq108875 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq102469 x y
       grind)
    | exact superpose eq102469 eq14
    | (have j1 := eq102469 x y
       grind)
    | exact resolve eq14 eq102469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108931 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq108875
       have i₂ := eq9848
       grind)
    | exact superpose eq9848 eq108875
    | exact resolve eq108875 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9848 eq108875
  have eq110153 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq108931
       have i₂ := eq10496
       grind)
    | exact superpose eq10496 eq108931
    | (have r₁ := eq108931
       have r₂ := eq10496
       grind)
    | exact resolve eq108931 eq10496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10496 eq108931
  have eq110156 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq110153
  have eq111995 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq110156
       grind)
    | exact superpose eq110156 eq28
    | (have j0 := eq28 y y
       grind)
    | exact resolve eq28 eq110156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110156
  have eq112040 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq111995
  have eq114041 : x ≠ y ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41401
       have i₂ := eq112040
       grind)
    | exact superpose eq112040 eq41401
    | (have r₁ := eq41401
       have r₂ := eq112040
       grind)
    | exact resolve eq41401 eq112040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114102 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq112040
  have eq114118 : x = (M.op y y) := by
    first
    | (have r₁ := eq114102
       have r₂ := eq71067
       grind)
    | exact resolve eq114102 eq71067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71067 eq114102
  have eq114124 : x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq114041
       have r₂ := eq70467
       grind)
    | exact resolve eq114041 eq70467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70467 eq114041
  have eq114126 : x = (M.op y x) := by
    first
    | (have r₁ := eq114124
       have r₂ := eq41401
       grind)
    | exact resolve eq114124 eq41401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41401 eq114124
  have eq115003 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq60041 y
       have i₂ := eq114118
       grind)
    | exact superpose eq114118 eq60041
    | exact resolve eq60041 eq114118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60041
  have eq115007 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16 y y
       have i₂ := eq114118
       grind)
    | exact superpose eq114118 eq16
    | exact resolve eq16 eq114118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq122836 : (σ y) = (M.op (σ y) (σ x)) ∨ (k y y) = (M.op y y) := by
    first
    | (have i₁ := eq3051 y
       have i₂ := eq115003
       grind)
    | exact superpose eq115003 eq3051
    | (have j0 := eq3051 y
       grind)
    | exact resolve eq3051 eq115003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3051
  have eq122849 : y ≠ (τ (M.op (σ y) (σ x))) ∨ y = (k y y) := by
    first
    | (have i₁ := eq35735 y
       have i₂ := eq115003
       grind)
    | exact superpose eq115003 eq35735
    | (have j0 := eq35735 y
       grind)
    | exact resolve eq35735 eq115003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35735
  have eq122850 : (M.op (σ y) (σ x)) = (σ (k y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq59691 y
       have i₂ := eq115003
       grind)
    | exact superpose eq115003 eq59691
    | (have j0 := eq59691 y
       grind)
    | exact resolve eq59691 eq115003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59691
  have eq122899 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq8 (σ y) (σ y)
       have i₂ := eq115003
       grind)
    | exact superpose eq115003 eq8
    | exact resolve eq8 eq115003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122924 : (M.op (σ y) (σ x)) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq122850
       have i₂ := eq114118
       grind)
    | exact superpose eq114118 eq122850
    | exact resolve eq122850 eq114118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122850
  have eq122925 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq122836
       have i₂ := eq114118
       grind)
    | exact superpose eq114118 eq122836
    | exact resolve eq122836 eq114118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122836
  have eq162407 : y ≠ (τ (σ y)) ∨ y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq122849
       have i₂ := eq122925
       grind)
    | exact superpose eq122925 eq122849
    | exact resolve eq122849 eq122925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122849 eq122925
  have eq162457 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have r₁ := eq162407
       have r₂ := eq9 y
       grind)
    | exact resolve eq162407 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162407
  have eq163956 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq162457
       grind)
    | exact superpose eq162457 eq28
    | (have j0 := eq28 y y
       grind)
    | exact resolve eq28 eq162457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq163964 : x ≠ y ∨ x = (k y y) := by grind
  clear eq162457
  have eq163965 : y = (M.op y y) ∨ x = (k y y) := by grind
  clear eq163956
  have eq163987 : x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq163965
       have i₂ := eq114118
       grind)
    | exact superpose eq114118 eq163965
    | exact resolve eq163965 eq114118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114118 eq163965
  have eq164010 : x = (k y y) := by
    first
    | (have r₁ := eq163987
       have r₂ := eq163964
       grind)
    | exact resolve eq163987 eq163964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163964 eq163987
  have eq165381 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq188 y
       have i₂ := eq164010
       grind)
    | exact superpose eq164010 eq188
    | (have j0 := eq188 y
       grind)
    | exact resolve eq188 eq164010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165472 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq165381
       have i₂ := eq115003
       grind)
    | exact superpose eq115003 eq165381
    | exact resolve eq165381 eq115003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115003 eq165381
  have eq183529 : (σ (k y y)) = (M.op (σ y) (σ (k y y))) ∨ x = y := by
    first
    | (have i₁ := eq122899
       have i₂ := eq122924
       grind)
    | exact superpose eq122924 eq122899
    | exact resolve eq122899 eq122924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122899 eq122924
  have eq183550 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq183529
       have i₂ := eq164010
       grind)
    | exact superpose eq164010 eq183529
    | exact resolve eq183529 eq164010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164010 eq183529
  have eq184343 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 (σ x) (σ y)
       have i₂ := eq183550
       grind)
    | exact superpose eq183550 eq8
    | exact resolve eq8 eq183550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183550
  have eq196164 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq184343
       grind)
    | exact superpose eq184343 eq14
    | exact resolve eq14 eq184343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184343
  have eq196194 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq196164
       have i₂ := eq115007
       grind)
    | exact superpose eq115007 eq196164
    | exact resolve eq196164 eq115007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115007 eq196164
  have eq197066 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq196194
       have i₂ := eq102469 x x
       grind)
    | exact superpose eq102469 eq196194
    | (have j1 := eq102469 x x
       grind)
    | exact resolve eq196194 eq102469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102469
  have eq197070 : x = (k x x) ∨ x = y := by
    first
    | (have j1 := eq815 x x
       grind)
    | (have r₁ := eq197066
       have r₂ := eq815 x x
       grind)
    | exact resolve eq197066 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815 eq197066
  have eq197642 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq188 x
       have i₂ := eq197070
       grind)
    | exact superpose eq197070 eq188
    | (have j0 := eq188 x
       grind)
    | exact resolve eq188 eq197070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq197665 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq15783 x
       have i₂ := eq197070
       grind)
    | exact superpose eq197070 eq15783
    | (have j0 := eq15783 x
       grind)
    | exact resolve eq15783 eq197070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15783 eq197070
  have eq197690 : (σ x) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq197665
  have eq197699 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq197642
  have eq208083 : (σ x) ≠ (σ (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq196194
       have i₂ := eq197699
       grind)
    | exact superpose eq197699 eq196194
    | exact resolve eq196194 eq197699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196194 eq197699
  have eq208172 : (σ x) ≠ (σ (M.op x x)) ∨ x = y := by grind
  clear eq208083
  have eq208208 : x = y := by
    first
    | (have r₁ := eq208172
       have r₂ := eq197690
       grind)
    | exact resolve eq208172 eq197690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197690 eq208172
  have eq209365 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq208208
       grind)
    | exact superpose eq208208 eq14
    | exact resolve eq14 eq208208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209443 : x = (M.op x x) := by
    first
    | (have i₁ := eq114126
       have i₂ := eq208208
       grind)
    | exact superpose eq208208 eq114126
    | exact resolve eq114126 eq208208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114126
  have eq209481 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq165472
       have i₂ := eq208208
       grind)
    | exact superpose eq208208 eq165472
    | exact resolve eq165472 eq208208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165472 eq208208
  have eq209487 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq209481
  have eq209524 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq209365
       have i₂ := eq209443
       grind)
    | exact superpose eq209443 eq209365
    | exact resolve eq209365 eq209443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209365 eq209443
  have eq209531 : False := by grind
  exact eq209531

/-- `Equation326`: `x ◇ y = x ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation326 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law326 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law326.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X1)) := by
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
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq26 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22
    | exact resolve eq22 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq30 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
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
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq66 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq25
    | exact resolve eq25 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq31
    | exact resolve eq31 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq86 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq26 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq26
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq43
  have eq131 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq117
    | exact resolve eq117 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq162 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (M.op X2 X0) = (k X0 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq30 X1 X0 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq30 X0 X0 X2
       grind)
    | exact superpose eq30 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq30 X2 X1 X0
       grind)
    | exact resolve eq12 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X2 (σ X1)) = (M.op X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq30 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 (σ X1) X2 (σ X0)
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq81 (M.op X1 X1) X0
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq81
    | (have j0 := eq81 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq81 (M.op X0 X0) X0
       have r₂ := eq8 X0 X0
       grind)
    | exact resolve eq81 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq308 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq131 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq131 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq131
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq131 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq33
    | (have j0 := eq33 X0 X1
       have j1 := eq33 X0 X1
       grind)
    | exact resolve eq33 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq33 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq33
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq9
    | (have j1 := eq33 X1 X0
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq131
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq131 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq391 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq394 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq380
    | (have j0 := eq380 X0 X1
       grind)
    | exact resolve eq380 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq988 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq391 (τ X0)
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq391
    | (have j0 := eq391 (τ X0)
       grind)
    | exact resolve eq391 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq990 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq988 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq988
    | (have j0 := eq988 X0
       grind)
    | exact resolve eq988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq993 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq990 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq990
    | (have j0 := eq990 X0
       grind)
    | exact resolve eq990 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1020 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq38
    | exact resolve eq38 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1069 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq10
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq10 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1103 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1020 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1020
    | (have j0 := eq1020 X0 X1
       grind)
    | exact resolve eq1020 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1132 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq993 (τ X0)
       have i₂ := eq66 X0 X0
       grind)
    | exact superpose eq66 eq993
    | (have j0 := eq993 (τ X0)
       grind)
    | exact resolve eq993 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1232 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq1255 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (σ (k (τ X1) X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1
       have i₂ := eq1103 X0 (τ X1)
       grind)
    | (have i₁ := eq26 X0
       have i₂ := eq1103 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact superpose eq1103 eq26
    | (have j1 := eq1103 X0 (τ X1)
       grind)
    | exact resolve eq26 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1260 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1255 X0 X1
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq1255
    | (have j0 := eq1255 X0 X1
       grind)
    | exact resolve eq1255 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq2083 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq75 y x
       grind)
    | exact superpose eq75 eq14
    | (have j1 := eq75 y x
       grind)
    | exact resolve eq14 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2088 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq75 X0 X0
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq2852 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq86
    | (have j0 := eq86 X1 (σ X0)
       grind)
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq2927 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2852 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2852
    | (have j0 := eq2852 X0 X1
       grind)
    | exact resolve eq2852 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852
  have eq3149 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq391 X0
       have i₂ := eq2927 X0 X0
       grind)
    | exact superpose eq2927 eq391
    | (have j0 := eq391 X0
       have j1 := eq2927 X0 X0
       grind)
    | (have r₁ := eq391 x
       have r₂ := eq2927 x x
       grind)
    | exact resolve eq391 eq2927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927
  have eq3176 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3149 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3149
  have eq6011 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (τ X0) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq308
    | (have j0 := eq308 X1 (τ X0)
       grind)
    | exact resolve eq308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq6111 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6011 X0 X1
       have i₂ := eq66 X1 X0
       grind)
    | exact superpose eq66 eq6011
    | (have j0 := eq6011 X0 X1
       grind)
    | exact resolve eq6011 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq6011
  have eq6457 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq162 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq6458 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq6457 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6457
  have eq6727 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq176 x y X0
       grind)
    | exact superpose eq176 eq14
    | (have j1 := eq176 x y X0
       grind)
    | exact resolve eq14 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq7565 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq394 x y
       grind)
    | exact superpose eq394 eq14
    | (have j1 := eq394 x y
       grind)
    | exact resolve eq14 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7574 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ X0)
       have i₂ := eq394 X0 X0
       grind)
    | exact superpose eq394 eq8
    | (have j1 := eq394 X0 X0
       grind)
    | exact resolve eq8 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq7632 : y = (k y x) := by
    first
    | (have j1 := eq1232 x y
       grind)
    | (have r₁ := eq7565
       have r₂ := eq1232 x y
       grind)
    | exact resolve eq7565 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7565
  have eq7855 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1103 x y
       have i₂ := eq7632
       grind)
    | exact superpose eq7632 eq1103
    | (have j0 := eq1103 x y
       grind)
    | exact resolve eq1103 eq7632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14341 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq342 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq342 X0 X1
       grind)
    | exact superpose eq342 eq9
    | (have j1 := eq342 X0 X1
       grind)
    | exact resolve eq9 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq14399 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14341 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq14341
    | (have j0 := eq14341 X0 X1
       grind)
    | exact resolve eq14341 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14341
  have eq14510 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1132 X0
       have i₂ := eq6111 X0 X0
       grind)
    | exact superpose eq6111 eq1132
    | (have j0 := eq1132 X0
       have j1 := eq6111 X0 X0
       grind)
    | (have r₁ := eq1132 x
       have r₂ := eq6111 x x
       grind)
    | exact resolve eq1132 eq6111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq6111
  have eq14518 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14510 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14510
  have eq19244 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14518 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq14518
    | (have j0 := eq14518 (σ X0)
       grind)
    | exact resolve eq14518 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14518
  have eq19385 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19244 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq19244
    | (have j0 := eq19244 X0
       grind)
    | exact resolve eq19244 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19244
  have eq28837 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X1 X1
       have i₂ := eq1103 X0 X1
       grind)
    | (have i₁ := eq187 X0 X1
       have i₂ := eq1103 (M.op X0 X1) X1
       grind)
    | exact superpose eq1103 eq187
    | (have j1 := eq1103 X0 X1
       grind)
    | (have r₁ := eq187 X1 X1
       have r₂ := eq1103 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq187 X0 X1
       have r₂ := eq1103 (M.op X0 X1) X1
       grind)
    | exact resolve eq187 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28839 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq187 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq187 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq187
    | (have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq187 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq187 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq187 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28991 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq187 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq29005 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28839 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28839
  have eq29007 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28837 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28837
  have eq30422 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq25 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq28991 (σ X0)
       grind)
    | exact superpose eq28991 eq25
    | exact resolve eq25 eq28991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq28991
  have eq31650 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq29005 (τ X0) X1
       grind)
    | exact superpose eq29005 eq19
    | (have j1 := eq29005 (τ X0) X1
       grind)
    | exact resolve eq19 eq29005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31754 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31650 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31650
    | (have j0 := eq31650 X0 X1
       grind)
    | exact resolve eq31650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31650
  have eq39660 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1069 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1069
    | (have j0 := eq1069 X1 (σ X0)
       grind)
    | exact resolve eq1069 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40015 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1069 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq40016 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq40015 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq40015
    | (have j0 := eq40015 X0
       grind)
    | exact resolve eq40015 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40015
  have eq40066 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39660 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq39660
    | (have j0 := eq39660 X0 X1
       grind)
    | exact resolve eq39660 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39660
  have eq40142 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40016 X0
       have i₂ := eq29005 X0 X0
       grind)
    | exact superpose eq29005 eq40016
    | (have j0 := eq40016 X0
       have j1 := eq29005 X0 X0
       grind)
    | (have r₁ := eq40016 x
       have r₂ := eq29005 x x
       grind)
    | exact resolve eq40016 eq29005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29005
  have eq40182 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq40142 X0
       have j1 := eq40016 X0
       grind)
    | (have r₁ := eq40142 X0
       have r₂ := eq40016 X0
       grind)
    | exact resolve eq40142 eq40016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40016 eq40142
  have eq40208 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2083
       have i₂ := eq6458 y x
       grind)
    | exact superpose eq6458 eq2083
    | (have j1 := eq6458 y x
       grind)
    | exact resolve eq2083 eq6458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083
  have eq40219 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq40208
  have eq40685 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq40182 (σ X0)
       have i₂ := eq3176 X0
       grind)
    | exact superpose eq3176 eq40182
    | (have j0 := eq40182 (σ X0)
       have j1 := eq3176 X0
       grind)
    | (have r₁ := eq40182 (σ X0)
       have r₂ := eq3176 X0
       grind)
    | exact resolve eq40182 eq3176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3176 eq40182
  have eq40699 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq40685 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40685
  have eq40708 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq40699 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq40699
    | (have j0 := eq40699 X0
       grind)
    | exact resolve eq40699 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40699
  have eq42234 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k X1 X1) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40708 X1
       have i₂ := eq1103 X0 X1
       grind)
    | (have i₁ := eq40708 X0
       have i₂ := eq1103 (M.op X0 X0) X1
       grind)
    | exact superpose eq1103 eq40708
    | (have j1 := eq1103 X0 X1
       grind)
    | exact resolve eq40708 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40708
  have eq46719 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30422 X0
       have i₂ := eq370 X0 X1
       grind)
    | (have i₁ := eq30422 X0
       have i₂ := eq370 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq370 eq30422
    | (have j1 := eq370 X1 X0
       grind)
    | exact resolve eq30422 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq30422
  have eq50798 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq31754 (σ X0) X1
       grind)
    | exact superpose eq31754 eq13
    | (have j1 := eq31754 (σ X0) X1
       grind)
    | exact resolve eq13 eq31754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31754
  have eq50975 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq50798 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq50798
    | (have j0 := eq50798 X0 X1
       grind)
    | exact resolve eq50798 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50798
  have eq54744 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq46719 x y
       grind)
    | exact superpose eq46719 eq14
    | (have j1 := eq46719 x y
       grind)
    | exact resolve eq14 eq46719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46719
  have eq54903 : x = (k x y) := by
    first
    | (have j1 := eq29007 x y
       grind)
    | (have r₁ := eq54744
       have r₂ := eq29007 x y
       grind)
    | exact resolve eq54744 eq29007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29007 eq54744
  have eq55199 : ∀ X0 : G, x = (M.op y x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq30 y X0 x
       have i₂ := eq54903
       grind)
    | exact superpose eq54903 eq30
    | (have j0 := eq30 y X0 x
       grind)
    | exact resolve eq30 eq54903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq56848 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq6727 X0
       have i₂ := eq6458 y x
       grind)
    | exact superpose eq6458 eq6727
    | (have j0 := eq6727 X0
       have j1 := eq6458 y x
       grind)
    | exact resolve eq6727 eq6458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6727
  have eq56860 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq56848 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56848
  have eq57386 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq56860 (σ x)
       grind)
    | exact superpose eq56860 eq14
    | exact resolve eq14 eq56860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56860
  have eq59627 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1260 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1260
    | (have j0 := eq1260 X1 (σ X0)
       grind)
    | exact resolve eq1260 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq59687 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59627 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq59627
    | (have j0 := eq59627 X0 X1
       grind)
    | exact resolve eq59627 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59627
  have eq59698 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59687 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq59687
    | (have j0 := eq59687 X0 X1
       grind)
    | exact resolve eq59687 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59687
  have eq61306 : (σ x) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq40066 y x
       have i₂ := eq54903
       grind)
    | exact superpose eq54903 eq40066
    | (have j0 := eq40066 y x
       grind)
    | exact resolve eq40066 eq54903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54903
  have eq61504 : (M.op y x) = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9 (M.op y x)
       have i₂ := eq61306
       grind)
    | exact superpose eq61306 eq9
    | exact resolve eq9 eq61306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61306
  have eq61541 : (σ y) = (σ (M.op x x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq61504
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq61504
    | exact resolve eq61504 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61504
  have eq63481 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq14399 x y
       grind)
    | exact superpose eq14399 eq14
    | (have j1 := eq14399 x y
       grind)
    | exact resolve eq14 eq14399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14399
  have eq63490 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq42234 x y
       grind)
    | (have r₁ := eq63481
       have r₂ := eq42234 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq63481
       have r₂ := eq42234 (k y x) (M.op x y)
       grind)
    | (have r₁ := eq63481
       have r₂ := eq42234 x y
       grind)
    | exact resolve eq63481 eq42234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42234 eq63481
  have eq63615 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50975 y y
       have i₂ := eq63490
       grind)
    | exact superpose eq63490 eq50975
    | exact resolve eq50975 eq63490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50975 eq63490
  have eq63619 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq63615
  have eq63634 : x = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55199 y
       have i₂ := eq63619
       grind)
    | exact superpose eq63619 eq55199
    | exact resolve eq55199 eq63619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55199 eq63619
  have eq63747 : x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq63634
  have eq65335 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq391 X0
       have i₂ := eq59698 X0 X0
       grind)
    | exact superpose eq59698 eq391
    | (have j0 := eq391 X0
       have j1 := eq59698 X0 X0
       grind)
    | (have r₁ := eq391 x
       have r₂ := eq59698 x x
       grind)
    | exact resolve eq391 eq59698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59698
  have eq65362 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq65335 X0
       have j1 := eq391 X0
       grind)
    | (have r₁ := eq65335 X0
       have r₂ := eq391 X0
       grind)
    | exact resolve eq65335 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq65335
  have eq65741 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq65362 x
       have i₂ := eq61541
       grind)
    | exact superpose eq61541 eq65362
    | (have j0 := eq65362 x
       grind)
    | exact resolve eq65362 eq61541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61541
  have eq65747 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq65741
       have r₂ := eq63747
       grind)
    | exact resolve eq65741 eq63747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65741
  have eq65774 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq57386
       have i₂ := eq65747
       grind)
    | exact superpose eq65747 eq57386
    | exact resolve eq57386 eq65747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57386 eq65747
  have eq65882 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) := by grind
  clear eq65774
  have eq66333 : (σ x) ≠ (σ y) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq65882
       have i₂ := eq40219
       grind)
    | exact superpose eq40219 eq65882
    | exact resolve eq65882 eq40219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40219 eq65882
  have eq66337 : (σ x) ≠ (σ y) ∨ x = (M.op y x) := by grind
  clear eq66333
  have eq66340 : x = (M.op y x) := by
    first
    | (have r₁ := eq66337
       have r₂ := eq63747
       grind)
    | exact resolve eq66337 eq63747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63747 eq66337
  have eq68789 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2088 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088
  have eq68790 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq68789 X0 X1
       have j1 := eq343 X1 X0
       grind)
    | (have r₁ := eq68789 (k X1 X1) X0
       have r₂ := eq343 X0 X1
       grind)
    | (have r₁ := eq68789 X0 (σ (k X1 X1))
       have r₂ := eq343 (σ X0) X1
       grind)
    | (have r₁ := eq68789 X1 X0
       have r₂ := eq343 X0 X1
       grind)
    | exact resolve eq68789 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq68789
  have eq68847 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X1)
       have i₂ := eq68790 (τ X1) X0
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq68790 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq68790 eq19
    | (have j1 := eq68790 (τ X1) X0
       grind)
    | exact resolve eq19 eq68790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq68848 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq68790 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq68790 X0 (σ X0)
       grind)
    | exact superpose eq68790 eq9
    | (have j1 := eq68790 X1 X0
       grind)
    | exact resolve eq9 eq68790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68790
  have eq68888 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq68847 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq68847
    | (have j0 := eq68847 X0 X1
       grind)
    | exact resolve eq68847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68847
  have eq68897 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq68888 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq68888
    | (have j0 := eq68888 X0 X1
       grind)
    | exact resolve eq68888 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68888
  have eq69770 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq68848 (σ X0) X1
       grind)
    | exact superpose eq68848 eq13
    | (have j1 := eq68848 (σ X0) X1
       grind)
    | exact resolve eq13 eq68848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68848
  have eq69795 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq69770 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq69770
    | (have j0 := eq69770 X0 X1
       grind)
    | exact resolve eq69770 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69770
  have eq71132 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq69795 x y
       grind)
    | exact superpose eq69795 eq14
    | (have j1 := eq69795 x y
       grind)
    | exact resolve eq14 eq69795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71224 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq71132
       have i₂ := eq7632
       grind)
    | exact superpose eq7632 eq71132
    | exact resolve eq71132 eq7632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7632 eq71132
  have eq71277 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq71224
       have i₂ := eq7855
       grind)
    | exact superpose eq7855 eq71224
    | (have r₁ := eq71224
       have r₂ := eq7855
       grind)
    | exact resolve eq71224 eq7855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7855 eq71224
  have eq71280 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq71277
  have eq71428 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq6458 y y
       have i₂ := eq71280
       grind)
    | exact superpose eq71280 eq6458
    | (have j0 := eq6458 y y
       grind)
    | exact resolve eq6458 eq71280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6458
  have eq71449 : x = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq68897 y y
       have i₂ := eq71280
       grind)
    | exact superpose eq71280 eq68897
    | exact resolve eq68897 eq71280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68897 eq71280
  have eq71454 : x = (M.op y y) ∨ x = y := by grind
  clear eq71449
  have eq71465 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq71428
  have eq72053 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq71465
  have eq72078 : x = (M.op y y) := by
    first
    | (have r₁ := eq72053
       have r₂ := eq71454
       grind)
    | exact resolve eq72053 eq71454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71454 eq72053
  have eq72100 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 y
       have i₂ := eq72078
       grind)
    | exact superpose eq72078 eq8
    | exact resolve eq8 eq72078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72214 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq65362 y
       have i₂ := eq72078
       grind)
    | exact superpose eq72078 eq65362
    | (have j0 := eq65362 y
       grind)
    | exact resolve eq65362 eq72078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72706 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) x)) ∨ (τ X0) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq38 X0 y
       have i₂ := eq72100 (τ X0)
       grind)
    | exact superpose eq72100 eq38
    | (have j0 := eq38 X0 y
       grind)
    | exact resolve eq38 eq72100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq72793 : ∀ X0 : G, (τ X0) = (M.op y x) ∨ (k (σ y) X0) = (σ (M.op (τ X0) x)) := by
    intro X0
    first
    | (have i₁ := eq72706 X0
       have i₂ := eq72100 y
       grind)
    | exact superpose eq72100 eq72706
    | (have j0 := eq72706 X0
       grind)
    | exact resolve eq72706 eq72100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72706
  have eq73113 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) x)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq72793 X0
       have i₂ := eq66340
       grind)
    | exact superpose eq66340 eq72793
    | (have j0 := eq72793 X0
       grind)
    | exact resolve eq72793 eq66340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72793
  have eq84946 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq73113 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq73113
    | exact resolve eq73113 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73113
  have eq84998 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 x)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq84946 X0
       have i₂ := eq13 y X0
       grind)
    | exact superpose eq13 eq84946
    | (have j0 := eq84946 X0
       grind)
    | exact resolve eq84946 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84946
  have eq85127 : ∀ X0 : G, (k y X0) = (τ (σ (M.op X0 x))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq9 (k y X0)
       have i₂ := eq84998 X0
       grind)
    | exact superpose eq84998 eq9
    | (have j1 := eq84998 X0
       grind)
    | exact resolve eq9 eq84998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84998
  have eq85170 : ∀ X0 : G, (k y X0) = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq85127 X0
       have i₂ := eq9 (M.op X0 x)
       grind)
    | exact superpose eq9 eq85127
    | (have j0 := eq85127 X0
       grind)
    | exact resolve eq85127 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85127
  have eq85361 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y x))) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq7574 y x
       have i₂ := eq85170 y
       grind)
    | exact superpose eq85170 eq7574
    | (have j1 := eq85170 y
       grind)
    | exact resolve eq7574 eq85170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7574 eq85170
  have eq85546 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq85361 X0
       have i₂ := eq66340
       grind)
    | exact superpose eq66340 eq85361
    | exact resolve eq85361 eq66340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85361
  have eq85597 : ∀ X0 : G, x = y ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq85546 X0
       have i₂ := eq66340
       grind)
    | exact superpose eq66340 eq85546
    | (have j0 := eq85546 X0
       grind)
    | exact resolve eq85546 eq66340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66340 eq85546
  have eq85598 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq85597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85597
  have eq85949 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq85598 (σ x)
       grind)
    | exact superpose eq85598 eq14
    | exact resolve eq14 eq85598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85598
  have eq85971 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq85949
       have i₂ := eq72100 x
       grind)
    | exact superpose eq72100 eq85949
    | exact resolve eq85949 eq72100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72100 eq85949
  have eq86681 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq85971
       have i₂ := eq69795 x x
       grind)
    | exact superpose eq69795 eq85971
    | (have j1 := eq69795 x x
       grind)
    | exact resolve eq85971 eq69795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69795
  have eq86684 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq85971
       have i₂ := eq19385 x
       grind)
    | exact superpose eq19385 eq85971
    | (have j1 := eq19385 x
       grind)
    | exact resolve eq85971 eq19385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19385
  have eq86696 : x = (M.op x x) ∨ x = y := by
    first
    | (have j1 := eq1103 x x
       grind)
    | (have r₁ := eq86684
       have r₂ := eq1103 x x
       grind)
    | exact resolve eq86684 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq86684
  have eq86698 : x = (k x x) ∨ x = y := by
    first
    | (have j1 := eq1232 x x
       grind)
    | (have r₁ := eq86681
       have r₂ := eq1232 x x
       grind)
    | exact resolve eq86681 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232 eq86681
  have eq86847 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq65362 x
       have i₂ := eq86696
       grind)
    | exact superpose eq86696 eq65362
    | (have j0 := eq65362 x
       grind)
    | exact resolve eq65362 eq86696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65362 eq86696
  have eq86916 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq86847
  have eq87063 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq40066 x x
       have i₂ := eq86698
       grind)
    | exact superpose eq86698 eq40066
    | (have j0 := eq40066 x x
       grind)
    | exact resolve eq40066 eq86698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40066 eq86698
  have eq87068 : (σ x) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq87063
  have eq88228 : (σ x) ≠ (σ (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq85971
       have i₂ := eq86916
       grind)
    | exact superpose eq86916 eq85971
    | exact resolve eq85971 eq86916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85971 eq86916
  have eq88392 : (σ x) ≠ (σ (M.op x x)) ∨ x = y := by grind
  clear eq88228
  have eq88445 : x = y := by
    first
    | (have r₁ := eq88392
       have r₂ := eq87068
       grind)
    | exact resolve eq88392 eq87068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87068 eq88392
  have eq88467 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq88445
       grind)
    | exact superpose eq88445 eq14
    | exact resolve eq14 eq88445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88542 : x = (M.op x x) := by
    first
    | (have i₁ := eq72078
       have i₂ := eq88445
       grind)
    | exact superpose eq88445 eq72078
    | exact resolve eq72078 eq88445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72078
  have eq88561 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72214
       have i₂ := eq88445
       grind)
    | exact superpose eq88445 eq72214
    | exact resolve eq72214 eq88445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72214 eq88445
  have eq88590 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq88561
  have eq88624 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq88467
       have i₂ := eq88542
       grind)
    | exact superpose eq88542 eq88467
    | exact resolve eq88467 eq88542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88467 eq88542
  have eq88627 : False := by grind
  exact eq88627
