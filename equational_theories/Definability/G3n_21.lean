import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if X = Y then m(Y,X) else if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_y_pyy_x_pyx_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq22 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    grind
  clear eq22
  have eq28 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq23
    | exact resolve eq23 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq28
    | (have j0 := eq28 X0
       grind)
    | exact resolve eq28 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 ∨ (k X1 X1) = X0 := by
    intro X0 X1
    grind
  clear eq38
  have eq48 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39 (σ x) (σ y)
       grind)
    | exact superpose eq39 eq16
    | (have j1 := eq39 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq48
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq48
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq50 : (σ y) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq49
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq49
    | exact resolve eq49 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq51 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq50
    | exact resolve eq50 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq64 : ∀ X1 : G, (k X1 X1) = X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  have eq65 : ∀ X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  clear eq64
  have eq66 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  clear eq65
  have eq67 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k (k X1 X1) X1) = (M.op X1 (k X1 X1)) ∨ (k X1 X1) = X1 := by
    intro X1
    grind
  clear eq66
  have eq82 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k x x)
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq23
    | (have j0 := eq23 X0
       have j1 := eq67 X0
       grind)
    | exact resolve eq23 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq83 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq82 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq51
       have i₂ := eq39 x y
       grind)
    | exact superpose eq39 eq51
    | (have j1 := eq39 x y
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq51 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq51
  have eq89 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq88
  have eq102 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq83
    | exact resolve eq83 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq252 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq253 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq252
  have eq254 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq253
  have eq255 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have r₁ := eq254
       have r₂ := eq15 x x
       grind)
    | exact resolve eq254 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq1468 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq83 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq83
    | exact resolve eq83 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1470 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq107 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq107
    | exact resolve eq107 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1473 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq1470
  have eq9091 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1473
       grind)
    | exact superpose eq1473 eq16
    | exact resolve eq16 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq24345 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq9091
       have i₂ := eq1468
       grind)
    | exact superpose eq1468 eq9091
    | exact resolve eq9091 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468 eq9091
  have eq24348 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ x = y := by grind
  clear eq24345
  have eq24349 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq24348
  have eq24350 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24349
       grind)
    | exact superpose eq24349 eq16
    | exact resolve eq16 eq24349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24349
  have eq24351 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq24350
  have eq24352 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq24351
  have eq24353 : x = (k y y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq24352
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24352 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24352
  have eq24477 : (M.op x y) = (k y x) ∨ x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23 y
       have i₂ := eq24353
       grind)
    | exact superpose eq24353 eq23
    | exact resolve eq23 eq24353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24478 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24353
       grind)
    | exact superpose eq24353 eq29
    | exact resolve eq29 eq24353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24353
  have eq24499 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24478
  have eq24811 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24499
       grind)
    | exact superpose eq24499 eq16
    | exact resolve eq16 eq24499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24499
  have eq24819 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24811
       have i₂ := eq24477
       grind)
    | exact superpose eq24477 eq24811
    | exact resolve eq24811 eq24477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24477 eq24811
  have eq24824 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq24819
  have eq24825 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24824
  have eq24828 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24825
       grind)
    | exact superpose eq24825 eq16
    | exact resolve eq16 eq24825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24825
  have eq24829 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24828
  have eq24830 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24829
  have eq24831 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq24830
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24830 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24830
  have eq24845 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq24831
       grind)
    | exact superpose eq24831 eq9
    | exact resolve eq9 eq24831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24831
  have eq25106 : y = (k x x) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24845
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq24845
    | exact resolve eq24845 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24845
  have eq25121 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq83 x
       have i₂ := eq25106
       grind)
    | exact superpose eq25106 eq83
    | exact resolve eq83 eq25106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq25124 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq107 x
       have i₂ := eq25106
       grind)
    | exact superpose eq25106 eq107
    | exact resolve eq107 eq25106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq25106
  have eq25137 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq25124
  have eq25163 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25137
       grind)
    | exact superpose eq25137 eq16
    | exact resolve eq16 eq25137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25137
  have eq25173 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25163
       have i₂ := eq25121
       grind)
    | exact superpose eq25121 eq25163
    | exact resolve eq25163 eq25121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25121 eq25163
  have eq25181 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq25173
  have eq25182 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25181
  have eq25185 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25182
       grind)
    | exact superpose eq25182 eq16
    | exact resolve eq16 eq25182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25182
  have eq25186 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25185
  have eq25187 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25186
  have eq25188 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq25187
       have r₂ := eq15 x x
       grind)
    | exact resolve eq25187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25187
  have eq25192 : y = (τ (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq25188
       grind)
    | exact superpose eq25188 eq9
    | exact resolve eq9 eq25188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25188
  have eq25453 : x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq25192
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq25192
    | exact resolve eq25192 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25192
  have eq25466 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25453
       grind)
    | exact superpose eq25453 eq16
    | exact resolve eq16 eq25453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25453
  have eq25467 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq25466
  have eq25468 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq25467
  have eq25469 : (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq25468
       have r₂ := eq15 x x
       grind)
    | exact resolve eq25468 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25468
  have eq25488 : (k y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq25469
       grind)
    | exact superpose eq25469 eq9
    | exact resolve eq9 eq25469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25469
  have eq25746 : x = (k y y) := by
    first
    | (have i₁ := eq25488
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq25488
    | exact resolve eq25488 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25488
  have eq25780 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq23 y
       have i₂ := eq25746
       grind)
    | exact superpose eq25746 eq23
    | exact resolve eq23 eq25746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq25781 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq25746
       grind)
    | exact superpose eq25746 eq29
    | exact resolve eq29 eq25746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25746
  have eq25834 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25781
       grind)
    | exact superpose eq25781 eq16
    | exact resolve eq16 eq25781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25781
  have eq25844 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25834
       have i₂ := eq25780
       grind)
    | exact superpose eq25780 eq25834
    | exact resolve eq25834 eq25780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25780 eq25834
  have eq25855 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq25844
  have eq25856 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25855
       grind)
    | exact superpose eq25855 eq16
    | exact resolve eq16 eq25855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25855
  have eq25859 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq25856
  have eq25860 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq25859
  have eq25861 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq25860
       have r₂ := eq15 x x
       grind)
    | exact resolve eq25860 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25860
  have eq25863 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq25861
       grind)
    | exact superpose eq25861 eq9
    | exact resolve eq9 eq25861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25861
  have eq26129 : x = y := by
    first
    | (have i₁ := eq25863
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq25863
    | exact resolve eq25863 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25863
  have eq26200 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26129
       grind)
    | exact superpose eq26129 eq16
    | exact resolve eq16 eq26129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26129
  have eq26203 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) := by grind
  clear eq26200
  have eq26204 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq26203
  have eq26205 : False := by grind
  exact eq26205

/-- `x □ y = if X = Y then m(Y,Y) else if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_y_pyy_x_pyy_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq22 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    grind
  clear eq22
  have eq28 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq23
    | exact resolve eq23 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq28
    | (have j0 := eq28 X0
       grind)
    | exact resolve eq28 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 ∨ (k X1 X1) = X0 := by
    intro X0 X1
    grind
  clear eq38
  have eq48 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39 (σ y) (σ x)
       grind)
    | exact superpose eq39 eq16
    | (have j1 := eq39 (σ y) (σ x)
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq48
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq48
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq50 : (σ x) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq49
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq49
    | exact resolve eq49 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq51 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq50
    | exact resolve eq50 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq64 : ∀ X1 : G, (k X1 X1) = X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k (M.op X1 X1) X1) = (M.op (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq65 : ∀ X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op (M.op X1 X1) X1) := by
    intro X1
    grind
  clear eq64
  have eq66 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op (M.op X1 X1) X1) := by
    intro X1
    grind
  clear eq65
  have eq67 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k (k X1 X1) X1) = (M.op (k X1 X1) X1) ∨ (k X1 X1) = X1 := by
    intro X1
    grind
  clear eq66
  have eq82 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k x x)
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq23
    | (have j0 := eq23 X0
       have j1 := eq67 X0
       grind)
    | exact resolve eq23 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq83 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq82 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq51
       have i₂ := eq39 y x
       grind)
    | exact superpose eq39 eq51
    | (have j1 := eq39 y x
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq51 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq51
  have eq89 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by grind
  clear eq88
  have eq102 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq83
    | exact resolve eq83 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq252 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq253 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by grind
  clear eq252
  have eq254 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by grind
  clear eq253
  have eq255 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have r₁ := eq254
       have r₂ := eq15 x x
       grind)
    | exact resolve eq254 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq1463 : x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq23 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq23
    | exact resolve eq23 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1464 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq29
    | exact resolve eq29 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1474 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq1464
  have eq8793 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1463
       grind)
    | exact superpose eq1463 eq16
    | exact resolve eq16 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463
  have eq8794 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq8793
  have eq8795 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq8794
  have eq8796 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have r₁ := eq8795
       have r₂ := eq15 x x
       grind)
    | exact resolve eq8795 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8795
  have eq9668 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1474
       grind)
    | exact superpose eq1474 eq16
    | exact resolve eq16 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq24491 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq9668
       have i₂ := eq8796
       grind)
    | exact superpose eq8796 eq9668
    | exact resolve eq9668 eq8796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8796 eq9668
  have eq24494 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24491
  have eq24495 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24494
  have eq24502 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq24495
       grind)
    | exact superpose eq24495 eq83
    | exact resolve eq83 eq24495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24505 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq24495
       grind)
    | exact superpose eq24495 eq107
    | exact resolve eq107 eq24495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24495
  have eq24518 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24505
  have eq24541 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24518
       grind)
    | exact superpose eq24518 eq16
    | exact resolve eq16 eq24518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24518
  have eq24557 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq24541
       have i₂ := eq24502
       grind)
    | exact superpose eq24502 eq24541
    | exact resolve eq24541 eq24502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24502 eq24541
  have eq24562 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = y := by grind
  clear eq24557
  have eq24563 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24562
  have eq24566 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24563
       grind)
    | exact superpose eq24563 eq16
    | exact resolve eq16 eq24563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24563
  have eq24567 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24566
  have eq24568 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24567
  have eq24569 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq24568
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24568 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24568
  have eq24573 : y = (τ (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq24569
       grind)
    | exact superpose eq24569 eq9
    | exact resolve eq9 eq24569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24569
  have eq24834 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq24573
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq24573
    | exact resolve eq24573 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24573
  have eq24847 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24834
       grind)
    | exact superpose eq24834 eq16
    | exact resolve eq16 eq24834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24834
  have eq24848 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24847
  have eq24849 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24848
  have eq24850 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq24849
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24849 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24849
  have eq24864 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq24850
       grind)
    | exact superpose eq24850 eq9
    | exact resolve eq9 eq24850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24850
  have eq25122 : y = (k x x) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq24864
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq24864
    | exact resolve eq24864 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24864
  have eq25133 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq23 x
       have i₂ := eq25122
       grind)
    | exact superpose eq25122 eq23
    | exact resolve eq23 eq25122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq25134 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq25122
       grind)
    | exact superpose eq25122 eq29
    | exact resolve eq29 eq25122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25122
  have eq30708 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25134
       grind)
    | exact superpose eq25134 eq16
    | exact resolve eq16 eq25134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25134
  have eq30724 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq30708
       have i₂ := eq25133
       grind)
    | exact superpose eq25133 eq30708
    | exact resolve eq30708 eq25133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25133 eq30708
  have eq30738 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq30724
  have eq30739 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30738
  have eq30746 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30739
       grind)
    | exact superpose eq30739 eq16
    | exact resolve eq16 eq30739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30739
  have eq30760 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30746
  have eq30761 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30760
  have eq30762 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq30761
       have r₂ := eq15 x x
       grind)
    | exact resolve eq30761 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30761
  have eq30766 : y = (τ (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq30762
       grind)
    | exact superpose eq30762 eq9
    | exact resolve eq9 eq30762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30762
  have eq31035 : x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq30766
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq30766
    | exact resolve eq30766 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30766
  have eq31048 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31035
       grind)
    | exact superpose eq31035 eq16
    | exact resolve eq16 eq31035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31035
  have eq31062 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq31048
  have eq31063 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq31062
  have eq31064 : (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq31063
       have r₂ := eq15 x x
       grind)
    | exact resolve eq31063 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31063
  have eq31084 : (k y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq31064
       grind)
    | exact superpose eq31064 eq9
    | exact resolve eq9 eq31064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31064
  have eq31350 : x = (k y y) := by
    first
    | (have i₁ := eq31084
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq31084
    | exact resolve eq31084 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31084
  have eq31389 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq31350
       grind)
    | exact superpose eq31350 eq83
    | exact resolve eq83 eq31350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq31392 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq31350
       grind)
    | exact superpose eq31350 eq107
    | exact resolve eq107 eq31350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq31350
  have eq31458 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31392
       grind)
    | exact superpose eq31392 eq16
    | exact resolve eq16 eq31392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31392
  have eq31476 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31458
       have i₂ := eq31389
       grind)
    | exact superpose eq31389 eq31458
    | exact resolve eq31458 eq31389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31389 eq31458
  have eq31478 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq31476
  have eq31491 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31478
       grind)
    | exact superpose eq31478 eq16
    | exact resolve eq16 eq31478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31478
  have eq31507 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq31491
  have eq31508 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq31507
  have eq31509 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq31508
       have r₂ := eq15 x x
       grind)
    | exact resolve eq31508 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31508
  have eq31512 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq31509
       grind)
    | exact superpose eq31509 eq9
    | exact resolve eq9 eq31509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31509
  have eq31786 : x = y := by
    first
    | (have i₁ := eq31512
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq31512
    | exact resolve eq31512 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31512
  have eq31858 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31786
       grind)
    | exact superpose eq31786 eq16
    | exact resolve eq16 eq31786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31786
  have eq31874 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) := by grind
  clear eq31858
  have eq31875 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq31874
  have eq31876 : False := by grind
  exact eq31876

/-- `x □ y = if X = Y then m(Y,Y) else if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_y_pyy_x_pyy_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq22 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    grind
  clear eq22
  have eq28 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq23
    | exact resolve eq23 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq28
    | (have j0 := eq28 X0
       grind)
    | exact resolve eq28 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 ∨ (k X1 X1) = X0 := by
    intro X0 X1
    grind
  clear eq38
  have eq48 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39 (σ x) (σ y)
       grind)
    | exact superpose eq39 eq16
    | (have j1 := eq39 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq48
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq48
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq50 : (σ y) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq49
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq49
    | exact resolve eq49 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq51 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq50
    | exact resolve eq50 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq64 : ∀ X1 : G, (k X1 X1) = X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  have eq65 : ∀ X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  clear eq64
  have eq66 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  clear eq65
  have eq67 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k (k X1 X1) X1) = (M.op X1 (k X1 X1)) ∨ (k X1 X1) = X1 := by
    intro X1
    grind
  clear eq66
  have eq82 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k x x)
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq23
    | (have j0 := eq23 X0
       have j1 := eq67 X0
       grind)
    | exact resolve eq23 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq83 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq82 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq51
       have i₂ := eq39 x y
       grind)
    | exact superpose eq39 eq51
    | (have j1 := eq39 x y
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq51 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq51
  have eq89 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq88
  have eq102 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq83
    | exact resolve eq83 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq252 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq253 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq252
  have eq254 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq253
  have eq255 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have r₁ := eq254
       have r₂ := eq15 x x
       grind)
    | exact resolve eq254 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq1468 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq83 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq83
    | exact resolve eq83 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1470 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq107 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq107
    | exact resolve eq107 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1473 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq1470
  have eq9091 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1473
       grind)
    | exact superpose eq1473 eq16
    | exact resolve eq16 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq24345 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq9091
       have i₂ := eq1468
       grind)
    | exact superpose eq1468 eq9091
    | exact resolve eq9091 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468 eq9091
  have eq24348 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ x = y := by grind
  clear eq24345
  have eq24349 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq24348
  have eq24350 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24349
       grind)
    | exact superpose eq24349 eq16
    | exact resolve eq16 eq24349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24349
  have eq24351 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq24350
  have eq24352 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq24351
  have eq24353 : x = (k y y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq24352
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24352 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24352
  have eq24477 : (M.op x y) = (k y x) ∨ x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23 y
       have i₂ := eq24353
       grind)
    | exact superpose eq24353 eq23
    | exact resolve eq23 eq24353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24478 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24353
       grind)
    | exact superpose eq24353 eq29
    | exact resolve eq29 eq24353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24353
  have eq24499 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24478
  have eq24811 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24499
       grind)
    | exact superpose eq24499 eq16
    | exact resolve eq16 eq24499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24499
  have eq24819 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24811
       have i₂ := eq24477
       grind)
    | exact superpose eq24477 eq24811
    | exact resolve eq24811 eq24477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24477 eq24811
  have eq24824 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq24819
  have eq24825 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24824
  have eq24828 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24825
       grind)
    | exact superpose eq24825 eq16
    | exact resolve eq16 eq24825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24825
  have eq24829 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24828
  have eq24830 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24829
  have eq24831 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq24830
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24830 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24830
  have eq24845 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq24831
       grind)
    | exact superpose eq24831 eq9
    | exact resolve eq9 eq24831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24831
  have eq25106 : y = (k x x) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24845
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq24845
    | exact resolve eq24845 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24845
  have eq25121 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq83 x
       have i₂ := eq25106
       grind)
    | exact superpose eq25106 eq83
    | exact resolve eq83 eq25106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq25124 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq107 x
       have i₂ := eq25106
       grind)
    | exact superpose eq25106 eq107
    | exact resolve eq107 eq25106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq25106
  have eq25137 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq25124
  have eq25163 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25137
       grind)
    | exact superpose eq25137 eq16
    | exact resolve eq16 eq25137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25137
  have eq25173 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25163
       have i₂ := eq25121
       grind)
    | exact superpose eq25121 eq25163
    | exact resolve eq25163 eq25121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25121 eq25163
  have eq25181 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq25173
  have eq25182 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25181
  have eq25185 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25182
       grind)
    | exact superpose eq25182 eq16
    | exact resolve eq16 eq25182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25182
  have eq25186 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25185
  have eq25187 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25186
  have eq25188 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq25187
       have r₂ := eq15 x x
       grind)
    | exact resolve eq25187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25187
  have eq25192 : y = (τ (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq25188
       grind)
    | exact superpose eq25188 eq9
    | exact resolve eq9 eq25188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25188
  have eq25453 : x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq25192
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq25192
    | exact resolve eq25192 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25192
  have eq25466 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25453
       grind)
    | exact superpose eq25453 eq16
    | exact resolve eq16 eq25453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25453
  have eq25467 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq25466
  have eq25468 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq25467
  have eq25469 : (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq25468
       have r₂ := eq15 x x
       grind)
    | exact resolve eq25468 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25468
  have eq25488 : (k y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq25469
       grind)
    | exact superpose eq25469 eq9
    | exact resolve eq9 eq25469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25469
  have eq25746 : x = (k y y) := by
    first
    | (have i₁ := eq25488
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq25488
    | exact resolve eq25488 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25488
  have eq25780 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq23 y
       have i₂ := eq25746
       grind)
    | exact superpose eq25746 eq23
    | exact resolve eq23 eq25746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq25781 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq25746
       grind)
    | exact superpose eq25746 eq29
    | exact resolve eq29 eq25746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25746
  have eq25834 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25781
       grind)
    | exact superpose eq25781 eq16
    | exact resolve eq16 eq25781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25781
  have eq25844 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25834
       have i₂ := eq25780
       grind)
    | exact superpose eq25780 eq25834
    | exact resolve eq25834 eq25780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25780 eq25834
  have eq25855 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq25844
  have eq25856 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25855
       grind)
    | exact superpose eq25855 eq16
    | exact resolve eq16 eq25855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25855
  have eq25859 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq25856
  have eq25860 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq25859
  have eq25861 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq25860
       have r₂ := eq15 x x
       grind)
    | exact resolve eq25860 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25860
  have eq25863 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq25861
       grind)
    | exact superpose eq25861 eq9
    | exact resolve eq9 eq25861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25861
  have eq26129 : x = y := by
    first
    | (have i₁ := eq25863
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq25863
    | exact resolve eq25863 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25863
  have eq26200 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26129
       grind)
    | exact superpose eq26129 eq16
    | exact resolve eq16 eq26129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26129
  have eq26203 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) := by grind
  clear eq26200
  have eq26204 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq26203
  have eq26205 : False := by grind
  exact eq26205

/-- `x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxy_pyy_pxx_pxy_pxx_pxx_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq47
  have eq52 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq61 : (M.op x y) ≠ (k y y) ∨ (k x x) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq48 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48
    | (have j0 := eq48 x y
       grind)
    | exact resolve eq48 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ x) (σ y)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq67
  have eq74 : (k (σ y) (σ y)) = (σ (k y y)) := by
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
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  clear eq86
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq87
  have eq96 : (M.op x y) = (k y y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq68 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq68
    | (have j0 := eq68 x y
       grind)
    | exact resolve eq68 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq68
    | (have j0 := eq68 (σ x) (σ y)
       grind)
    | exact resolve eq68 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (k X1 X1) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (σ (k X0 X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq68
    | (have j0 := eq68 X1 (σ X0)
       grind)
    | exact resolve eq68 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 X0
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq48
    | (have j0 := eq48 X1 X0
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq48 X0 X0
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq68 (M.op X0 X1) (k X1 X1)
       grind)
    | exact resolve eq48 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq107 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq108 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X1 X0) ∨ (k X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq130 : (M.op x y) ≠ (k x x) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq88 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | (have j0 := eq88 x y
       grind)
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq88
    | (have j0 := eq88 (σ x) (σ y)
       grind)
    | exact resolve eq88 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq542 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq61
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq61
    | (have r₁ := eq61
       have r₂ := eq96
       grind)
    | exact resolve eq61 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq74
    | exact resolve eq74 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq544 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq542
  have eq545 : (k x x) = (k x y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq544
  have eq546 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq21 eq543
    | exact resolve eq543 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq569 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq97 eq62
    | (have r₁ := eq62
       have r₂ := eq97
       grind)
    | exact resolve eq62 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq569
  have eq572 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq571
  have eq962 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq108 X1 X0
       grind)
    | exact superpose eq108 eq48
    | (have j0 := eq48 X0 X1
       have j1 := eq108 X1 X0
       grind)
    | (have r₁ := eq48 X1 X1
       have r₂ := eq108 X1 X1
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq108 (M.op X0 X1) (k X1 X1)
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq108 (k X1 X1) (M.op X0 X1)
       grind)
    | exact resolve eq48 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq108
  have eq966 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq962 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq1186 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 (σ X1)) ∨ (k X0 X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq98 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1187 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (σ (k X1 X1)) ∨ (k X0 X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq98 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq3896 : ∀ X0 : G, (σ (k X0 y)) ≠ (k (σ y) (σ y)) ∨ (σ (k X0 y)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (σ y) ∨ (k (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq41 eq966
    | (have j0 := eq966 (σ X0) (σ y)
       grind)
    | exact resolve eq966 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq966
  have eq3904 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 X0)) ∨ (σ (k X0 y)) ≠ (k (σ y) (σ y)) ∨ (σ X0) = (σ y) ∨ (k (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3896 X0
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq3896
    | (have j0 := eq3896 X0
       grind)
    | (have r₁ := eq3896 y
       have r₂ := eq10 y y
       grind)
    | exact resolve eq3896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896
  have eq3916 : ∀ X0 : G, (σ (k X0 y)) ≠ (k (σ y) (σ y)) ∨ (σ (k X0 y)) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq3904 X0
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq3904
    | (have j0 := eq3904 X0
       grind)
    | (have r₁ := eq3904 y
       have r₂ := eq10 y y
       grind)
    | exact resolve eq3904 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904
  have eq4877 : ∀ X0 : G, (k X0 X0) ≠ (k X0 (σ y)) ∨ (k X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ (k y y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1186 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1186
    | (have j0 := eq1186 X0 y
       grind)
    | exact resolve eq1186 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq4888 : ∀ X0 : G, (k X0 X0) ≠ (k X0 (σ y)) ∨ (k (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (k X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq4877 X0
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq4877
    | (have j0 := eq4877 X0
       grind)
    | exact resolve eq4877 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4877
  have eq5504 : ∀ X0 : G, (σ (k x X0)) ≠ (σ (k X0 X0)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (σ (k X0 X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq1187
    | (have j0 := eq1187 (σ x) X0
       grind)
    | (have r₁ := eq1187 (σ x) x
       have r₂ := eq36 x
       grind)
    | exact resolve eq1187 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1187
  have eq20759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq546 eq97
    | exact resolve eq97 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq20789 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq20759
       have r₂ := eq28
       grind)
    | exact resolve eq20759 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20759
  have eq20797 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq20789 eq56
    | exact resolve eq56 eq20789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20789
  have eq20808 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq20797
       have i₂ := eq545
       grind)
    | exact superpose eq545 eq20797
    | exact resolve eq20797 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20797
  have eq20832 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq20808
  have eq21112 : (k (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq20832
       grind)
    | exact superpose eq20832 eq44
    | exact resolve eq44 eq20832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20832
  have eq21173 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq21112
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq21112
    | exact resolve eq21112 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21112
  have eq21174 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq21173
  have eq21207 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq21174 eq131
    | (have r₁ := eq131
       have r₂ := eq21174
       grind)
    | exact resolve eq131 eq21174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21174
  have eq21231 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq21207
  have eq21232 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq21231
  have eq30534 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq546 eq21232
    | exact resolve eq21232 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq21232
  have eq30568 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq30534
  have eq30579 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq30568
       have r₂ := eq28
       grind)
    | exact resolve eq30568 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30568
  have eq30584 : (τ (σ (M.op x y))) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq30579 eq56
    | exact resolve eq56 eq30579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30579
  have eq30609 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq31 eq30584
    | exact resolve eq30584 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq30584
  have eq30610 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq30609
  have eq30617 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq30610
       grind)
    | exact superpose eq30610 eq45
    | exact resolve eq45 eq30610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30652 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq30617
    | exact resolve eq30617 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30617
  have eq30940 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq30652 eq572
    | exact resolve eq572 eq30652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq30948 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq30940
  have eq30952 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq30948
       have r₂ := eq28
       grind)
    | exact resolve eq30948 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30948
  have eq223259 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq30652 eq4888
    | (have j0 := eq4888 (σ x)
       grind)
    | exact resolve eq4888 eq30652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4888
  have eq223269 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq223259
  have eq223272 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq223269
    | exact resolve eq223269 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223269
  have eq223298 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq223272
    | exact resolve eq223272 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223272
  have eq223323 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq223298
       have r₂ := eq30952
       grind)
    | exact resolve eq223298 eq30952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30952 eq223298
  have eq223346 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq223323 eq62
    | (have r₁ := eq62
       have r₂ := eq223323
       grind)
    | exact resolve eq62 eq223323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223323
  have eq223380 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq223346
  have eq223381 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq223380
  have eq223472 : (k x y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq223381 eq56
    | exact resolve eq56 eq223381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223381
  have eq223819 : (k x x) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq52 eq223472
    | exact resolve eq223472 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223472
  have eq223988 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq30610
       have i₂ := eq223819
       grind)
    | exact superpose eq223819 eq30610
    | exact resolve eq30610 eq223819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30610 eq223819
  have eq224266 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq223988
  have eq224315 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq224266 eq131
    | (have r₁ := eq131
       have r₂ := eq224266
       grind)
    | exact resolve eq131 eq224266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq224342 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq224315
  have eq224343 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq224342
  have eq240486 : (τ (k (σ x) (σ y))) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq224343 eq85
    | exact resolve eq85 eq224343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq224343
  have eq240540 : (k x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq56 eq240486
    | exact resolve eq240486 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240486
  have eq240895 : (M.op x y) ≠ (k x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq61
       have i₂ := eq240540
       grind)
    | exact superpose eq240540 eq61
    | exact resolve eq61 eq240540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240540
  have eq240937 : (M.op x y) ≠ (k x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by grind
  clear eq240895
  have eq240959 : (k x x) = (k x y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq240937
       have r₂ := eq545
       grind)
    | exact resolve eq240937 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq240937
  have eq253304 : (σ (k x x)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq240959
       grind)
    | exact superpose eq240959 eq45
    | exact resolve eq45 eq240959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240959
  have eq253634 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq253304
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq253304
    | exact resolve eq253304 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253304
  have eq253642 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq253634
       have r₂ := eq62
       grind)
    | exact resolve eq253634 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq253634
  have eq254145 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq253642 eq30652
    | exact resolve eq30652 eq253642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30652 eq253642
  have eq254458 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq254145
  have eq254855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq254458 eq224266
    | exact resolve eq224266 eq254458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224266 eq254458
  have eq254935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq254855
  have eq254964 : (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq254935
       have r₂ := eq28
       grind)
    | exact resolve eq254935 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254935
  have eq254980 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq254964
       grind)
    | exact superpose eq254964 eq44
    | exact resolve eq44 eq254964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254984 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq130
       have i₂ := eq254964
       grind)
    | exact superpose eq254964 eq130
    | (have r₁ := eq130
       have r₂ := eq254964
       grind)
    | exact resolve eq130 eq254964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq254964
  have eq255027 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq254984
  have eq255028 : (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq255027
  have eq255057 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq254980
    | exact resolve eq254980 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254980
  have eq283600 : (σ (k x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq255028
       grind)
    | exact superpose eq255028 eq74
    | exact resolve eq74 eq255028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq283645 : (σ (k x y)) ≠ (σ (k x y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5504 y
       have i₂ := eq255028
       grind)
    | exact superpose eq255028 eq5504
    | (have j0 := eq5504 y
       grind)
    | exact resolve eq5504 eq255028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255028
  have eq283652 : (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq283645
  have eq283670 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq283652
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq283652
    | exact resolve eq283652 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283652
  have eq283691 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq283600
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq283600
    | exact resolve eq283600 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283600
  have eq283693 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq283670
    | exact resolve eq283670 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283670
  have eq283703 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq283693
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq283693
    | exact resolve eq283693 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283693
  have eq283704 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq283703
  have eq283714 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq283704
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq283704
    | exact resolve eq283704 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283704
  have eq283722 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq283714
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq283714
    | exact resolve eq283714 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283714
  have eq283727 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq27 eq283722
    | exact resolve eq283722 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283722
  have eq375610 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq283727 eq56
    | exact resolve eq56 eq283727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1030361 : (k (σ y) (σ y)) ≠ (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq3916 x
       have i₂ := eq375610
       grind)
    | exact superpose eq375610 eq3916
    | (have j0 := eq3916 x
       grind)
    | exact resolve eq3916 eq375610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3916 eq375610
  have eq1030558 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030361
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq1030361
    | exact resolve eq1030361 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030361
  have eq1030604 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030558
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq1030558
    | exact resolve eq1030558 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030558
  have eq1030635 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030604
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1030604
    | exact resolve eq1030604 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030604
  have eq1030636 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq1030635
  have eq1030649 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030636
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1030636
    | exact resolve eq1030636 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030636
  have eq1030662 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030649
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1030649
    | exact resolve eq1030649 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030649
  have eq1030672 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq27 eq1030662
    | exact resolve eq1030662 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030662
  have eq1030673 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq1030672
  have eq1030681 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030673
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1030673
    | exact resolve eq1030673 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030673
  have eq1030682 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq1030681
  have eq1030695 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq283691 eq1030682
    | exact resolve eq1030682 eq283691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283691 eq1030682
  have eq1030696 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq1030695
  have eq1030706 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have r₁ := eq1030696
       have r₂ := eq283727
       grind)
    | exact resolve eq1030696 eq283727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283727 eq1030696
  have eq1032157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq1030706 eq255057
    | exact resolve eq255057 eq1030706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030706
  have eq1032635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) := by grind
  clear eq1032157
  have eq1032664 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1032635
       have r₂ := eq28
       grind)
    | exact resolve eq1032635 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032635
  have eq1032676 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq61
       have i₂ := eq1032664
       grind)
    | exact superpose eq1032664 eq61
    | (have r₁ := eq61
       have r₂ := eq1032664
       grind)
    | exact resolve eq61 eq1032664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1032751 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5504 y
       have i₂ := eq1032664
       grind)
    | exact superpose eq1032664 eq5504
    | (have j0 := eq5504 y
       grind)
    | exact resolve eq5504 eq1032664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5504 eq1032664
  have eq1032822 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1032676
  have eq1032823 : (k x x) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1032822
  have eq1032837 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1032751
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq1032751
    | exact resolve eq1032751 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032751
  have eq1032886 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq1032837
    | exact resolve eq1032837 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032837
  have eq1032914 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1032886
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1032886
    | exact resolve eq1032886 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032886
  have eq1032941 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1032914
    | exact resolve eq1032914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032914
  have eq1032964 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1032941
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1032941
    | exact resolve eq1032941 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032941
  have eq1032965 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1032964
  have eq1032980 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1032965
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1032965
    | exact resolve eq1032965 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032965
  have eq1032986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq1032980
    | exact resolve eq1032980 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032980
  have eq1032990 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq1032986
    | exact resolve eq1032986 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032986
  have eq1032992 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1032990
       have r₂ := eq28
       grind)
    | exact resolve eq1032990 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032990
  have eq1033642 : (σ (k x x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq1032823
       grind)
    | exact superpose eq1032823 eq45
    | exact resolve eq45 eq1032823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1032823
  have eq1034032 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1033642
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1033642
    | exact resolve eq1033642 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1033642
  have eq1040592 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1034032 eq1032992
    | exact resolve eq1032992 eq1034032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032992 eq1034032
  have eq1040593 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1040592
  have eq1040604 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1040593
       have r₂ := eq255057
       grind)
    | exact resolve eq1040593 eq255057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040593
  have eq1040657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1040604 eq255057
    | exact resolve eq255057 eq1040604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255057 eq1040604
  have eq1041137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1040657
  have eq1041165 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1041137
       have r₂ := eq28
       grind)
    | exact resolve eq1041137 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041137
  have eq1041177 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1041165 eq30
    | exact resolve eq30 eq1041165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1041165
  have eq1041435 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1041177
    | exact resolve eq1041177 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1041177
  have eq1041436 : x = y := by grind
  clear eq1041435
  have eq1041440 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1041436
       grind)
    | exact superpose eq1041436 eq19
    | exact resolve eq19 eq1041436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1041441 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1041436
       grind)
    | exact superpose eq1041436 eq25
    | exact resolve eq25 eq1041436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1041436
  have eq1041860 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1041441
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1041441
    | exact resolve eq1041441 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1041441
  have eq1041861 : (M.op x y) = (k x x) := by grind
  clear eq1041440
  have eq1041862 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1041860 eq27
    | exact resolve eq27 eq1041860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1041860
  have eq1042235 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1041862
  have eq1042594 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1042235 eq52
    | exact resolve eq52 eq1042235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1042235
  have eq1042933 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1042594
       have i₂ := eq1041861
       grind)
    | exact superpose eq1041861 eq1042594
    | exact resolve eq1042594 eq1041861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041861 eq1042594
  have eq1042995 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1042933 eq15
    | exact resolve eq15 eq1042933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042933
  have eq1043693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1042995
    | exact resolve eq1042995 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1042995
  have eq1043863 : False := by grind
  exact eq1043863

/-- `x □ y = if X = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxy_pyy_pxx_pxy_pxy_pxx_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq47
  have eq52 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq61 : (M.op x y) ≠ (k y y) ∨ (k x x) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq48 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48
    | (have j0 := eq48 x y
       grind)
    | exact resolve eq48 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ x) (σ y)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq67
  have eq74 : (k (σ y) (σ y)) = (σ (k y y)) := by
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
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  clear eq86
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq87
  have eq96 : (M.op x y) = (k y y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq68 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq68
    | (have j0 := eq68 x y
       grind)
    | exact resolve eq68 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq68
    | (have j0 := eq68 (σ x) (σ y)
       grind)
    | exact resolve eq68 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (k X1 X1) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (σ (k X0 X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq68
    | (have j0 := eq68 X1 (σ X0)
       grind)
    | exact resolve eq68 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 X0
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq48
    | (have j0 := eq48 X1 X0
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq48 X0 X0
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq68 (M.op X0 X1) (k X1 X1)
       grind)
    | exact resolve eq48 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq107 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq108 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X1 X0) ∨ (k X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq130 : (M.op x y) ≠ (k x x) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq88 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | (have j0 := eq88 x y
       grind)
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq88
    | (have j0 := eq88 (σ x) (σ y)
       grind)
    | exact resolve eq88 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq542 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq61
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq61
    | (have r₁ := eq61
       have r₂ := eq96
       grind)
    | exact resolve eq61 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq74
    | exact resolve eq74 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq544 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq542
  have eq545 : (k x x) = (k x y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq544
  have eq546 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq21 eq543
    | exact resolve eq543 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq569 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq97 eq62
    | (have r₁ := eq62
       have r₂ := eq97
       grind)
    | exact resolve eq62 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq569
  have eq572 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq571
  have eq962 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq108 X1 X0
       grind)
    | exact superpose eq108 eq48
    | (have j0 := eq48 X0 X1
       have j1 := eq108 X1 X0
       grind)
    | (have r₁ := eq48 X1 X1
       have r₂ := eq108 X1 X1
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq108 (M.op X0 X1) (k X1 X1)
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq108 (k X1 X1) (M.op X0 X1)
       grind)
    | exact resolve eq48 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq108
  have eq966 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq962 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq1186 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 (σ X1)) ∨ (k X0 X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq98 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1187 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (σ (k X1 X1)) ∨ (k X0 X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq98 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq3896 : ∀ X0 : G, (σ (k X0 y)) ≠ (k (σ y) (σ y)) ∨ (σ (k X0 y)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (σ y) ∨ (k (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq41 eq966
    | (have j0 := eq966 (σ X0) (σ y)
       grind)
    | exact resolve eq966 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq966
  have eq3904 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 X0)) ∨ (σ (k X0 y)) ≠ (k (σ y) (σ y)) ∨ (σ X0) = (σ y) ∨ (k (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3896 X0
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq3896
    | (have j0 := eq3896 X0
       grind)
    | (have r₁ := eq3896 y
       have r₂ := eq10 y y
       grind)
    | exact resolve eq3896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896
  have eq3916 : ∀ X0 : G, (σ (k X0 y)) ≠ (k (σ y) (σ y)) ∨ (σ (k X0 y)) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq3904 X0
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq3904
    | (have j0 := eq3904 X0
       grind)
    | (have r₁ := eq3904 y
       have r₂ := eq10 y y
       grind)
    | exact resolve eq3904 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904
  have eq4877 : ∀ X0 : G, (k X0 X0) ≠ (k X0 (σ y)) ∨ (k X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ (k y y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1186 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1186
    | (have j0 := eq1186 X0 y
       grind)
    | exact resolve eq1186 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq4888 : ∀ X0 : G, (k X0 X0) ≠ (k X0 (σ y)) ∨ (k (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (k X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq4877 X0
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq4877
    | (have j0 := eq4877 X0
       grind)
    | exact resolve eq4877 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4877
  have eq5504 : ∀ X0 : G, (σ (k x X0)) ≠ (σ (k X0 X0)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (σ (k X0 X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq1187
    | (have j0 := eq1187 (σ x) X0
       grind)
    | (have r₁ := eq1187 (σ x) x
       have r₂ := eq36 x
       grind)
    | exact resolve eq1187 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1187
  have eq20759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq546 eq97
    | exact resolve eq97 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq20789 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq20759
       have r₂ := eq28
       grind)
    | exact resolve eq20759 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20759
  have eq20797 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq20789 eq56
    | exact resolve eq56 eq20789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20789
  have eq20808 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq20797
       have i₂ := eq545
       grind)
    | exact superpose eq545 eq20797
    | exact resolve eq20797 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20797
  have eq20832 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq20808
  have eq21112 : (k (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq20832
       grind)
    | exact superpose eq20832 eq44
    | exact resolve eq44 eq20832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20832
  have eq21173 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq21112
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq21112
    | exact resolve eq21112 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21112
  have eq21174 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq21173
  have eq21207 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq21174 eq131
    | (have r₁ := eq131
       have r₂ := eq21174
       grind)
    | exact resolve eq131 eq21174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21174
  have eq21231 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq21207
  have eq21232 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq21231
  have eq30534 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq546 eq21232
    | exact resolve eq21232 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq21232
  have eq30568 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq30534
  have eq30579 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq30568
       have r₂ := eq28
       grind)
    | exact resolve eq30568 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30568
  have eq30584 : (τ (σ (M.op x y))) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq30579 eq56
    | exact resolve eq56 eq30579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30579
  have eq30609 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq31 eq30584
    | exact resolve eq30584 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq30584
  have eq30610 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq30609
  have eq30617 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq30610
       grind)
    | exact superpose eq30610 eq45
    | exact resolve eq45 eq30610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30652 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq30617
    | exact resolve eq30617 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30617
  have eq30940 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq30652 eq572
    | exact resolve eq572 eq30652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq30948 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq30940
  have eq30952 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq30948
       have r₂ := eq28
       grind)
    | exact resolve eq30948 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30948
  have eq223259 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq30652 eq4888
    | (have j0 := eq4888 (σ x)
       grind)
    | exact resolve eq4888 eq30652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4888
  have eq223269 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq223259
  have eq223272 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq223269
    | exact resolve eq223269 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223269
  have eq223298 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq223272
    | exact resolve eq223272 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223272
  have eq223323 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq223298
       have r₂ := eq30952
       grind)
    | exact resolve eq223298 eq30952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30952 eq223298
  have eq223346 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq223323 eq62
    | (have r₁ := eq62
       have r₂ := eq223323
       grind)
    | exact resolve eq62 eq223323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223323
  have eq223380 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq223346
  have eq223381 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq223380
  have eq223472 : (k x y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq223381 eq56
    | exact resolve eq56 eq223381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223381
  have eq223819 : (k x x) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq52 eq223472
    | exact resolve eq223472 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223472
  have eq223988 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq30610
       have i₂ := eq223819
       grind)
    | exact superpose eq223819 eq30610
    | exact resolve eq30610 eq223819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30610 eq223819
  have eq224266 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq223988
  have eq224315 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq224266 eq131
    | (have r₁ := eq131
       have r₂ := eq224266
       grind)
    | exact resolve eq131 eq224266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq224342 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq224315
  have eq224343 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq224342
  have eq240486 : (τ (k (σ x) (σ y))) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq224343 eq85
    | exact resolve eq85 eq224343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq224343
  have eq240540 : (k x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq56 eq240486
    | exact resolve eq240486 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240486
  have eq240895 : (M.op x y) ≠ (k x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq61
       have i₂ := eq240540
       grind)
    | exact superpose eq240540 eq61
    | exact resolve eq61 eq240540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240540
  have eq240937 : (M.op x y) ≠ (k x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by grind
  clear eq240895
  have eq240959 : (k x x) = (k x y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq240937
       have r₂ := eq545
       grind)
    | exact resolve eq240937 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq240937
  have eq253304 : (σ (k x x)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq240959
       grind)
    | exact superpose eq240959 eq45
    | exact resolve eq45 eq240959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240959
  have eq253634 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq253304
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq253304
    | exact resolve eq253304 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253304
  have eq253642 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq253634
       have r₂ := eq62
       grind)
    | exact resolve eq253634 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq253634
  have eq254145 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq253642 eq30652
    | exact resolve eq30652 eq253642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30652 eq253642
  have eq254458 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq254145
  have eq254855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq254458 eq224266
    | exact resolve eq224266 eq254458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224266 eq254458
  have eq254935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq254855
  have eq254964 : (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq254935
       have r₂ := eq28
       grind)
    | exact resolve eq254935 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254935
  have eq254980 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq254964
       grind)
    | exact superpose eq254964 eq44
    | exact resolve eq44 eq254964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254984 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq130
       have i₂ := eq254964
       grind)
    | exact superpose eq254964 eq130
    | (have r₁ := eq130
       have r₂ := eq254964
       grind)
    | exact resolve eq130 eq254964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq254964
  have eq255027 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq254984
  have eq255028 : (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq255027
  have eq255057 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq254980
    | exact resolve eq254980 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254980
  have eq283600 : (σ (k x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq255028
       grind)
    | exact superpose eq255028 eq74
    | exact resolve eq74 eq255028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq283645 : (σ (k x y)) ≠ (σ (k x y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5504 y
       have i₂ := eq255028
       grind)
    | exact superpose eq255028 eq5504
    | (have j0 := eq5504 y
       grind)
    | exact resolve eq5504 eq255028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255028
  have eq283652 : (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq283645
  have eq283670 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq283652
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq283652
    | exact resolve eq283652 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283652
  have eq283691 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq283600
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq283600
    | exact resolve eq283600 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283600
  have eq283693 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq283670
    | exact resolve eq283670 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283670
  have eq283703 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq283693
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq283693
    | exact resolve eq283693 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283693
  have eq283704 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq283703
  have eq283714 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq283704
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq283704
    | exact resolve eq283704 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283704
  have eq283722 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq283714
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq283714
    | exact resolve eq283714 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283714
  have eq283727 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq27 eq283722
    | exact resolve eq283722 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283722
  have eq375610 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq283727 eq56
    | exact resolve eq56 eq283727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1030361 : (k (σ y) (σ y)) ≠ (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq3916 x
       have i₂ := eq375610
       grind)
    | exact superpose eq375610 eq3916
    | (have j0 := eq3916 x
       grind)
    | exact resolve eq3916 eq375610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3916 eq375610
  have eq1030558 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030361
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq1030361
    | exact resolve eq1030361 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030361
  have eq1030604 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030558
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq1030558
    | exact resolve eq1030558 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030558
  have eq1030635 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030604
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1030604
    | exact resolve eq1030604 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030604
  have eq1030636 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq1030635
  have eq1030649 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030636
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1030636
    | exact resolve eq1030636 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030636
  have eq1030662 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030649
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1030649
    | exact resolve eq1030649 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030649
  have eq1030672 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq27 eq1030662
    | exact resolve eq1030662 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030662
  have eq1030673 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq1030672
  have eq1030681 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030673
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1030673
    | exact resolve eq1030673 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030673
  have eq1030682 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq1030681
  have eq1030695 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq283691 eq1030682
    | exact resolve eq1030682 eq283691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283691 eq1030682
  have eq1030696 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq1030695
  have eq1030706 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have r₁ := eq1030696
       have r₂ := eq283727
       grind)
    | exact resolve eq1030696 eq283727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283727 eq1030696
  have eq1032157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq1030706 eq255057
    | exact resolve eq255057 eq1030706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030706
  have eq1032635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) := by grind
  clear eq1032157
  have eq1032664 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1032635
       have r₂ := eq28
       grind)
    | exact resolve eq1032635 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032635
  have eq1032676 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq61
       have i₂ := eq1032664
       grind)
    | exact superpose eq1032664 eq61
    | (have r₁ := eq61
       have r₂ := eq1032664
       grind)
    | exact resolve eq61 eq1032664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1032751 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5504 y
       have i₂ := eq1032664
       grind)
    | exact superpose eq1032664 eq5504
    | (have j0 := eq5504 y
       grind)
    | exact resolve eq5504 eq1032664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5504 eq1032664
  have eq1032822 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1032676
  have eq1032823 : (k x x) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1032822
  have eq1032837 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1032751
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq1032751
    | exact resolve eq1032751 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032751
  have eq1032886 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq1032837
    | exact resolve eq1032837 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032837
  have eq1032914 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1032886
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1032886
    | exact resolve eq1032886 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032886
  have eq1032941 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1032914
    | exact resolve eq1032914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032914
  have eq1032964 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1032941
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1032941
    | exact resolve eq1032941 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032941
  have eq1032965 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1032964
  have eq1032980 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1032965
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1032965
    | exact resolve eq1032965 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032965
  have eq1032986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq1032980
    | exact resolve eq1032980 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032980
  have eq1032990 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq1032986
    | exact resolve eq1032986 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032986
  have eq1032992 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1032990
       have r₂ := eq28
       grind)
    | exact resolve eq1032990 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032990
  have eq1033642 : (σ (k x x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq1032823
       grind)
    | exact superpose eq1032823 eq45
    | exact resolve eq45 eq1032823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1032823
  have eq1034032 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1033642
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1033642
    | exact resolve eq1033642 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1033642
  have eq1040592 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1034032 eq1032992
    | exact resolve eq1032992 eq1034032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032992 eq1034032
  have eq1040593 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1040592
  have eq1040604 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1040593
       have r₂ := eq255057
       grind)
    | exact resolve eq1040593 eq255057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040593
  have eq1040657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1040604 eq255057
    | exact resolve eq255057 eq1040604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255057 eq1040604
  have eq1041137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1040657
  have eq1041165 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1041137
       have r₂ := eq28
       grind)
    | exact resolve eq1041137 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041137
  have eq1041177 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1041165 eq30
    | exact resolve eq30 eq1041165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1041165
  have eq1041435 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1041177
    | exact resolve eq1041177 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1041177
  have eq1041436 : x = y := by grind
  clear eq1041435
  have eq1041440 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1041436
       grind)
    | exact superpose eq1041436 eq19
    | exact resolve eq19 eq1041436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1041441 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1041436
       grind)
    | exact superpose eq1041436 eq25
    | exact resolve eq25 eq1041436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1041436
  have eq1041860 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1041441
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1041441
    | exact resolve eq1041441 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1041441
  have eq1041861 : (M.op x y) = (k x x) := by grind
  clear eq1041440
  have eq1041862 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1041860 eq27
    | exact resolve eq27 eq1041860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1041860
  have eq1042235 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1041862
  have eq1042594 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1042235 eq52
    | exact resolve eq52 eq1042235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1042235
  have eq1042933 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1042594
       have i₂ := eq1041861
       grind)
    | exact superpose eq1041861 eq1042594
    | exact resolve eq1042594 eq1041861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041861 eq1042594
  have eq1042995 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1042933 eq15
    | exact resolve eq15 eq1042933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042933
  have eq1043693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1042995
    | exact resolve eq1042995 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1042995
  have eq1043863 : False := by grind
  exact eq1043863

/-- `x □ y = if X = Y then m(Y,X) else if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxy_pyy_pxx_pxy_pyx_pxx_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq47
  have eq52 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq61 : (M.op x y) ≠ (k y y) ∨ (k x x) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq48 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48
    | (have j0 := eq48 x y
       grind)
    | exact resolve eq48 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ x) (σ y)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq48
    | (have j0 := eq48 X1 (σ X0)
       grind)
    | exact resolve eq48 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq67
  have eq74 : (k (σ y) (σ y)) = (σ (k y y)) := by
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
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  clear eq86
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq87
  have eq96 : (M.op x y) = (k y y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq68 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq68
    | (have j0 := eq68 x y
       grind)
    | exact resolve eq68 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq68
    | (have j0 := eq68 (σ x) (σ y)
       grind)
    | exact resolve eq68 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (k X1 X1) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (σ (k X0 X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq68
    | (have j0 := eq68 X1 (σ X0)
       grind)
    | exact resolve eq68 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq130 : (M.op x y) ≠ (k x x) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq88 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | (have j0 := eq88 x y
       grind)
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq88
    | (have j0 := eq88 (σ x) (σ y)
       grind)
    | exact resolve eq88 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq542 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq61
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq61
    | (have r₁ := eq61
       have r₂ := eq96
       grind)
    | exact resolve eq61 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq74
    | exact resolve eq74 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq544 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq542
  have eq545 : (k x x) = (k x y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq544
  have eq546 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq21 eq543
    | exact resolve eq543 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq569 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq97 eq62
    | (have r₁ := eq62
       have r₂ := eq97
       grind)
    | exact resolve eq62 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq569
  have eq572 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq571
  have eq1213 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (σ (k X1 X1)) ∨ (k X0 X0) = (k X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 X0
       have i₂ := eq98 X1 X0
       grind)
    | exact superpose eq98 eq63
    | (have j0 := eq63 X1 X0
       have j1 := eq98 X1 X0
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq98 (k X0 X0) (M.op X1 (σ X0))
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq98 X0 X1
       grind)
    | exact resolve eq63 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1217 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 (σ X1)) ∨ (k X0 X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq98 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1218 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (σ (k X1 X1)) ∨ (k X0 X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq98 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1222 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (σ (k X1 X1)) ∨ (k X0 X0) = (k X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1213 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq1227 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (σ (k X1 X1)) ∨ (k X0 X0) = (k X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1222 X0 X1
       have j1 := eq63 X1 X0
       grind)
    | (have r₁ := eq1222 X0 X1
       have r₂ := eq63 (k X1 X1) (k X0 (σ X1))
       grind)
    | (have r₁ := eq1222 (M.op X1 (σ X0)) (k X0 X0)
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq1222 X1 X0
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq1222 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1222
  have eq4854 : ∀ X0 : G, (k X0 X0) ≠ (k X0 (σ y)) ∨ (k X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ (k y y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1217 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1217
    | (have j0 := eq1217 X0 y
       grind)
    | exact resolve eq1217 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq4865 : ∀ X0 : G, (k X0 X0) ≠ (k X0 (σ y)) ∨ (k (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (k X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq4854 X0
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq4854
    | (have j0 := eq4854 X0
       grind)
    | exact resolve eq4854 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq4854
  have eq4994 : ∀ X0 : G, (σ (k x X0)) ≠ (σ (k X0 X0)) ∨ (σ (k x X0)) = (k (σ x) (σ x)) ∨ (σ X0) = (σ x) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq1227
    | (have j0 := eq1227 (σ x) X0
       grind)
    | (have r₁ := eq1227 (σ x) x
       have r₂ := eq36 x
       grind)
    | exact resolve eq1227 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq5611 : ∀ X0 : G, (σ (k x X0)) ≠ (σ (k X0 X0)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (σ (k X0 X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq1218
    | (have j0 := eq1218 (σ x) X0
       grind)
    | (have r₁ := eq1218 (σ x) x
       have r₂ := eq36 x
       grind)
    | exact resolve eq1218 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1218
  have eq27506 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq546 eq97
    | exact resolve eq97 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq27535 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq27506
       have r₂ := eq28
       grind)
    | exact resolve eq27506 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27506
  have eq27543 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq27535 eq56
    | exact resolve eq56 eq27535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27535
  have eq27554 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq27543
       have i₂ := eq545
       grind)
    | exact superpose eq545 eq27543
    | exact resolve eq27543 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27543
  have eq27585 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq27554
  have eq27889 : (k (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq27585
       grind)
    | exact superpose eq27585 eq44
    | exact resolve eq44 eq27585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27585
  have eq27961 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq27889
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq27889
    | exact resolve eq27889 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27889
  have eq27962 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq27961
  have eq27998 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq27962 eq131
    | (have r₁ := eq131
       have r₂ := eq27962
       grind)
    | exact resolve eq131 eq27962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27962
  have eq28021 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq27998
  have eq28022 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq28021
  have eq37683 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq546 eq28022
    | exact resolve eq28022 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq28022
  have eq37716 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq37683
  have eq37727 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq37716
       have r₂ := eq28
       grind)
    | exact resolve eq37716 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37716
  have eq37732 : (τ (σ (M.op x y))) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq37727 eq56
    | exact resolve eq56 eq37727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37727
  have eq37757 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq31 eq37732
    | exact resolve eq37732 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq37732
  have eq37758 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq37757
  have eq37765 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq37758
       grind)
    | exact superpose eq37758 eq45
    | exact resolve eq45 eq37758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37814 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq37765
    | exact resolve eq37765 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37765
  have eq38112 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq37814 eq572
    | exact resolve eq572 eq37814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq38120 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq38112
  have eq38124 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq38120
       have r₂ := eq28
       grind)
    | exact resolve eq38120 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38120
  have eq236014 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq37814 eq4865
    | (have j0 := eq4865 (σ x)
       grind)
    | exact resolve eq4865 eq37814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4865
  have eq236024 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq236014
  have eq236027 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq236024
    | exact resolve eq236024 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236024
  have eq236053 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq236027
    | exact resolve eq236027 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236027
  have eq236078 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq236053
       have r₂ := eq38124
       grind)
    | exact resolve eq236053 eq38124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38124 eq236053
  have eq236102 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq236078 eq62
    | (have r₁ := eq62
       have r₂ := eq236078
       grind)
    | exact resolve eq62 eq236078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236078
  have eq236137 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq236102
  have eq236138 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq236137
  have eq236266 : (k x y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq236138 eq56
    | exact resolve eq56 eq236138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236138
  have eq236627 : (k x x) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq52 eq236266
    | exact resolve eq236266 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236266
  have eq236807 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq37758
       have i₂ := eq236627
       grind)
    | exact superpose eq236627 eq37758
    | exact resolve eq37758 eq236627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37758 eq236627
  have eq237085 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq236807
  have eq237141 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq237085 eq131
    | (have r₁ := eq131
       have r₂ := eq237085
       grind)
    | exact resolve eq131 eq237085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq237167 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq237141
  have eq237168 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq237167
  have eq254676 : (τ (k (σ x) (σ y))) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq237168 eq85
    | exact resolve eq85 eq237168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq237168
  have eq254729 : (k x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq56 eq254676
    | exact resolve eq254676 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq254676
  have eq254820 : (M.op x y) ≠ (k x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq61
       have i₂ := eq254729
       grind)
    | exact superpose eq254729 eq61
    | exact resolve eq61 eq254729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254729
  have eq254871 : (M.op x y) ≠ (k x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by grind
  clear eq254820
  have eq254904 : (k x x) = (k x y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq254871
       have r₂ := eq545
       grind)
    | exact resolve eq254871 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq254871
  have eq262185 : (σ (k x x)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq254904
       grind)
    | exact superpose eq254904 eq45
    | exact resolve eq45 eq254904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254904
  have eq262527 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq262185
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq262185
    | exact resolve eq262185 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262185
  have eq262534 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq262527
       have r₂ := eq62
       grind)
    | exact resolve eq262527 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq262527
  have eq263116 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq262534 eq37814
    | exact resolve eq37814 eq262534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37814 eq262534
  have eq263429 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq263116
  have eq263850 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq263429 eq237085
    | exact resolve eq237085 eq263429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237085 eq263429
  have eq263927 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq263850
  have eq263956 : (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq263927
       have r₂ := eq28
       grind)
    | exact resolve eq263927 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263927
  have eq263972 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq263956
       grind)
    | exact superpose eq263956 eq44
    | exact resolve eq44 eq263956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263976 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq130
       have i₂ := eq263956
       grind)
    | exact superpose eq263956 eq130
    | (have r₁ := eq130
       have r₂ := eq263956
       grind)
    | exact resolve eq130 eq263956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq263956
  have eq264021 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq263976
  have eq264022 : (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq264021
  have eq264057 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq263972
    | exact resolve eq263972 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263972
  have eq297629 : (σ (k x y)) ≠ (σ (k x y)) ∨ (k (σ x) (σ x)) = (σ (k x y)) ∨ (σ y) = (σ x) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4994 y
       have i₂ := eq264022
       grind)
    | exact superpose eq264022 eq4994
    | (have j0 := eq4994 y
       grind)
    | exact resolve eq4994 eq264022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4994
  have eq297636 : (σ (k x y)) ≠ (σ (k x y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5611 y
       have i₂ := eq264022
       grind)
    | exact superpose eq264022 eq5611
    | (have j0 := eq5611 y
       grind)
    | exact resolve eq5611 eq264022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264022
  have eq297641 : (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq297636
  have eq297646 : (k (σ x) (σ x)) = (σ (k x y)) ∨ (σ y) = (σ x) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq297629
  have eq297660 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq297641
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq297641
    | exact resolve eq297641 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297641
  have eq297663 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq297646
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq297646
    | exact resolve eq297646 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297646
  have eq297698 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq297660
    | exact resolve eq297660 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297660
  have eq297701 : (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq297663
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq297663
    | exact resolve eq297663 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297663
  have eq297702 : (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq297701
  have eq297711 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq297698
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq297698
    | exact resolve eq297698 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297698
  have eq297712 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq297711
  have eq297716 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq297702
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq297702
    | exact resolve eq297702 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297702
  have eq297725 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq297712
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq297712
    | exact resolve eq297712 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297712
  have eq297727 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq27 eq297716
    | exact resolve eq297716 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297716
  have eq297735 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq297725
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq297725
    | exact resolve eq297725 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297725
  have eq297740 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq27 eq297735
    | exact resolve eq297735 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297735
  have eq965679 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq297727 eq297740
    | exact resolve eq297740 eq297727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297727 eq297740
  have eq965721 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq965679
  have eq965990 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq965721 eq264057
    | exact resolve eq264057 eq965721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965721
  have eq966485 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) := by grind
  clear eq965990
  have eq966522 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq966485
       have r₂ := eq28
       grind)
    | exact resolve eq966485 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966485
  have eq966537 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq61
       have i₂ := eq966522
       grind)
    | exact superpose eq966522 eq61
    | (have r₁ := eq61
       have r₂ := eq966522
       grind)
    | exact resolve eq61 eq966522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq966635 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5611 y
       have i₂ := eq966522
       grind)
    | exact superpose eq966522 eq5611
    | (have j0 := eq5611 y
       grind)
    | exact resolve eq5611 eq966522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5611 eq966522
  have eq966715 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq966537
  have eq966716 : (k x x) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq966715
  have eq966729 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq966635
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq966635
    | exact resolve eq966635 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966635
  have eq966797 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq966729
    | exact resolve eq966729 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966729
  have eq966831 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq966797
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq966797
    | exact resolve eq966797 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966797
  have eq966862 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq966831
    | exact resolve eq966831 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966831
  have eq966890 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq966862
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq966862
    | exact resolve eq966862 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966862
  have eq966891 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq966890
  have eq966906 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq966891
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq966891
    | exact resolve eq966891 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966891
  have eq966911 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq966906
    | exact resolve eq966906 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966906
  have eq966914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq966911
    | exact resolve eq966911 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966911
  have eq966916 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq966914
       have r₂ := eq28
       grind)
    | exact resolve eq966914 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966914
  have eq967297 : (σ (k x x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq966716
       grind)
    | exact superpose eq966716 eq45
    | exact resolve eq45 eq966716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq966716
  have eq967708 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq967297
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq967297
    | exact resolve eq967297 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq967297
  have eq970619 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq967708 eq966916
    | exact resolve eq966916 eq967708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966916 eq967708
  have eq970620 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq970619
  have eq970632 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq970620
       have r₂ := eq264057
       grind)
    | exact resolve eq970620 eq264057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970620
  have eq970694 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq970632 eq264057
    | exact resolve eq264057 eq970632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264057 eq970632
  have eq971189 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq970694
  have eq971222 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq971189
       have r₂ := eq28
       grind)
    | exact resolve eq971189 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971189
  have eq971231 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq971222 eq30
    | exact resolve eq30 eq971222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq971222
  have eq971483 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq971231
    | exact resolve eq971231 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq971231
  have eq971484 : x = y := by grind
  clear eq971483
  have eq975722 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq971484
       grind)
    | exact superpose eq971484 eq19
    | exact resolve eq19 eq971484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq975723 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq971484
       grind)
    | exact superpose eq971484 eq25
    | exact resolve eq25 eq971484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq971484
  have eq976235 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq975723
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq975723
    | exact resolve eq975723 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq975723
  have eq976236 : (M.op x y) = (k x x) := by grind
  clear eq975722
  have eq976237 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq976235 eq27
    | exact resolve eq27 eq976235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq976235
  have eq976597 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq976237
  have eq978296 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq976597 eq52
    | exact resolve eq52 eq976597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq976597
  have eq978652 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq978296
       have i₂ := eq976236
       grind)
    | exact superpose eq976236 eq978296
    | exact resolve eq978296 eq976236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976236 eq978296
  have eq978716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq978652 eq15
    | exact resolve eq15 eq978652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978652
  have eq979335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq978716
    | exact resolve eq978716 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq978716
  have eq979493 : False := by grind
  exact eq979493

/-- `x □ y = if X = Y then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxy_pyy_pxx_pxy_pyy_pxx_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq47
  have eq52 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq61 : (M.op x y) ≠ (k y y) ∨ (k x x) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq48 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48
    | (have j0 := eq48 x y
       grind)
    | exact resolve eq48 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ x) (σ y)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq67
  have eq74 : (k (σ y) (σ y)) = (σ (k y y)) := by
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
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  clear eq86
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq87
  have eq96 : (M.op x y) = (k y y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq68 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq68
    | (have j0 := eq68 x y
       grind)
    | exact resolve eq68 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq68
    | (have j0 := eq68 (σ x) (σ y)
       grind)
    | exact resolve eq68 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (k X1 X1) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (σ (k X0 X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq68
    | (have j0 := eq68 X1 (σ X0)
       grind)
    | exact resolve eq68 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 X0
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq48
    | (have j0 := eq48 X1 X0
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq48 X0 X0
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq68 (M.op X0 X1) (k X1 X1)
       grind)
    | exact resolve eq48 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq107 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq108 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X1 X0) ∨ (k X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq130 : (M.op x y) ≠ (k x x) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq88 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | (have j0 := eq88 x y
       grind)
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq88
    | (have j0 := eq88 (σ x) (σ y)
       grind)
    | exact resolve eq88 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq542 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq61
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq61
    | (have r₁ := eq61
       have r₂ := eq96
       grind)
    | exact resolve eq61 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq74
    | exact resolve eq74 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq544 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq542
  have eq545 : (k x x) = (k x y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq544
  have eq546 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq21 eq543
    | exact resolve eq543 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq569 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq97 eq62
    | (have r₁ := eq62
       have r₂ := eq97
       grind)
    | exact resolve eq62 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq569
  have eq572 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq571
  have eq962 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq108 X1 X0
       grind)
    | exact superpose eq108 eq48
    | (have j0 := eq48 X0 X1
       have j1 := eq108 X1 X0
       grind)
    | (have r₁ := eq48 X1 X1
       have r₂ := eq108 X1 X1
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq108 (M.op X0 X1) (k X1 X1)
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq108 (k X1 X1) (M.op X0 X1)
       grind)
    | exact resolve eq48 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq108
  have eq966 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq962 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq1186 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 (σ X1)) ∨ (k X0 X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq98 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1187 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (σ (k X1 X1)) ∨ (k X0 X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X0 (σ X1)) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq98 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq3896 : ∀ X0 : G, (σ (k X0 y)) ≠ (k (σ y) (σ y)) ∨ (σ (k X0 y)) = (k (σ X0) (σ X0)) ∨ (σ X0) = (σ y) ∨ (k (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq41 eq966
    | (have j0 := eq966 (σ X0) (σ y)
       grind)
    | exact resolve eq966 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq966
  have eq3904 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 X0)) ∨ (σ (k X0 y)) ≠ (k (σ y) (σ y)) ∨ (σ X0) = (σ y) ∨ (k (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3896 X0
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq3896
    | (have j0 := eq3896 X0
       grind)
    | (have r₁ := eq3896 y
       have r₂ := eq10 y y
       grind)
    | exact resolve eq3896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896
  have eq3916 : ∀ X0 : G, (σ (k X0 y)) ≠ (k (σ y) (σ y)) ∨ (σ (k X0 y)) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq3904 X0
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq3904
    | (have j0 := eq3904 X0
       grind)
    | (have r₁ := eq3904 y
       have r₂ := eq10 y y
       grind)
    | exact resolve eq3904 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904
  have eq4877 : ∀ X0 : G, (k X0 X0) ≠ (k X0 (σ y)) ∨ (k X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ (k y y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1186 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1186
    | (have j0 := eq1186 X0 y
       grind)
    | exact resolve eq1186 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq4888 : ∀ X0 : G, (k X0 X0) ≠ (k X0 (σ y)) ∨ (k (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (k X0 X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq4877 X0
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq4877
    | (have j0 := eq4877 X0
       grind)
    | exact resolve eq4877 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4877
  have eq5504 : ∀ X0 : G, (σ (k x X0)) ≠ (σ (k X0 X0)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (σ (k X0 X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq1187
    | (have j0 := eq1187 (σ x) X0
       grind)
    | (have r₁ := eq1187 (σ x) x
       have r₂ := eq36 x
       grind)
    | exact resolve eq1187 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1187
  have eq20759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq546 eq97
    | exact resolve eq97 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq20789 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq20759
       have r₂ := eq28
       grind)
    | exact resolve eq20759 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20759
  have eq20797 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq20789 eq56
    | exact resolve eq56 eq20789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20789
  have eq20808 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq20797
       have i₂ := eq545
       grind)
    | exact superpose eq545 eq20797
    | exact resolve eq20797 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20797
  have eq20832 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq20808
  have eq21112 : (k (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq20832
       grind)
    | exact superpose eq20832 eq44
    | exact resolve eq44 eq20832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20832
  have eq21173 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq21112
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq21112
    | exact resolve eq21112 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21112
  have eq21174 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq21173
  have eq21207 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq21174 eq131
    | (have r₁ := eq131
       have r₂ := eq21174
       grind)
    | exact resolve eq131 eq21174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21174
  have eq21231 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq21207
  have eq21232 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq21231
  have eq30534 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq546 eq21232
    | exact resolve eq21232 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq21232
  have eq30568 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq30534
  have eq30579 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq30568
       have r₂ := eq28
       grind)
    | exact resolve eq30568 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30568
  have eq30584 : (τ (σ (M.op x y))) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq30579 eq56
    | exact resolve eq56 eq30579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30579
  have eq30609 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq31 eq30584
    | exact resolve eq30584 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq30584
  have eq30610 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq30609
  have eq30617 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq30610
       grind)
    | exact superpose eq30610 eq45
    | exact resolve eq45 eq30610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30652 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq30617
    | exact resolve eq30617 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30617
  have eq30940 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq30652 eq572
    | exact resolve eq572 eq30652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq30948 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq30940
  have eq30952 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq30948
       have r₂ := eq28
       grind)
    | exact resolve eq30948 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30948
  have eq223259 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq30652 eq4888
    | (have j0 := eq4888 (σ x)
       grind)
    | exact resolve eq4888 eq30652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4888
  have eq223269 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq223259
  have eq223272 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq223269
    | exact resolve eq223269 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223269
  have eq223298 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq223272
    | exact resolve eq223272 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223272
  have eq223323 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq223298
       have r₂ := eq30952
       grind)
    | exact resolve eq223298 eq30952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30952 eq223298
  have eq223346 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq223323 eq62
    | (have r₁ := eq62
       have r₂ := eq223323
       grind)
    | exact resolve eq62 eq223323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223323
  have eq223380 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq223346
  have eq223381 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq223380
  have eq223472 : (k x y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq223381 eq56
    | exact resolve eq56 eq223381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223381
  have eq223819 : (k x x) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq52 eq223472
    | exact resolve eq223472 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223472
  have eq223988 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq30610
       have i₂ := eq223819
       grind)
    | exact superpose eq223819 eq30610
    | exact resolve eq30610 eq223819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30610 eq223819
  have eq224266 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq223988
  have eq224315 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq224266 eq131
    | (have r₁ := eq131
       have r₂ := eq224266
       grind)
    | exact resolve eq131 eq224266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq224342 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq224315
  have eq224343 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq224342
  have eq240486 : (τ (k (σ x) (σ y))) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq224343 eq85
    | exact resolve eq85 eq224343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq224343
  have eq240540 : (k x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq56 eq240486
    | exact resolve eq240486 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240486
  have eq240895 : (M.op x y) ≠ (k x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq61
       have i₂ := eq240540
       grind)
    | exact superpose eq240540 eq61
    | exact resolve eq61 eq240540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240540
  have eq240937 : (M.op x y) ≠ (k x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by grind
  clear eq240895
  have eq240959 : (k x x) = (k x y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq240937
       have r₂ := eq545
       grind)
    | exact resolve eq240937 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq240937
  have eq253304 : (σ (k x x)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq240959
       grind)
    | exact superpose eq240959 eq45
    | exact resolve eq45 eq240959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240959
  have eq253634 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq253304
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq253304
    | exact resolve eq253304 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253304
  have eq253642 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq253634
       have r₂ := eq62
       grind)
    | exact resolve eq253634 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq253634
  have eq254145 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq253642 eq30652
    | exact resolve eq30652 eq253642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30652 eq253642
  have eq254458 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq254145
  have eq254855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq254458 eq224266
    | exact resolve eq224266 eq254458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224266 eq254458
  have eq254935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x x) := by grind
  clear eq254855
  have eq254964 : (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq254935
       have r₂ := eq28
       grind)
    | exact resolve eq254935 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254935
  have eq254980 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq254964
       grind)
    | exact superpose eq254964 eq44
    | exact resolve eq44 eq254964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254984 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq130
       have i₂ := eq254964
       grind)
    | exact superpose eq254964 eq130
    | (have r₁ := eq130
       have r₂ := eq254964
       grind)
    | exact resolve eq130 eq254964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq254964
  have eq255027 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq254984
  have eq255028 : (k x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq255027
  have eq255057 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq254980
    | exact resolve eq254980 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254980
  have eq283600 : (σ (k x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq255028
       grind)
    | exact superpose eq255028 eq74
    | exact resolve eq74 eq255028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq283645 : (σ (k x y)) ≠ (σ (k x y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5504 y
       have i₂ := eq255028
       grind)
    | exact superpose eq255028 eq5504
    | (have j0 := eq5504 y
       grind)
    | exact resolve eq5504 eq255028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255028
  have eq283652 : (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq283645
  have eq283670 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq283652
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq283652
    | exact resolve eq283652 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283652
  have eq283691 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq283600
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq283600
    | exact resolve eq283600 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283600
  have eq283693 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq283670
    | exact resolve eq283670 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283670
  have eq283703 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq283693
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq283693
    | exact resolve eq283693 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283693
  have eq283704 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq283703
  have eq283714 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq283704
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq283704
    | exact resolve eq283704 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283704
  have eq283722 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq283714
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq283714
    | exact resolve eq283714 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283714
  have eq283727 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq27 eq283722
    | exact resolve eq283722 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283722
  have eq375610 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq283727 eq56
    | exact resolve eq56 eq283727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1030361 : (k (σ y) (σ y)) ≠ (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq3916 x
       have i₂ := eq375610
       grind)
    | exact superpose eq375610 eq3916
    | (have j0 := eq3916 x
       grind)
    | exact resolve eq3916 eq375610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3916 eq375610
  have eq1030558 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030361
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq1030361
    | exact resolve eq1030361 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030361
  have eq1030604 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030558
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq1030558
    | exact resolve eq1030558 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030558
  have eq1030635 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030604
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1030604
    | exact resolve eq1030604 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030604
  have eq1030636 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq1030635
  have eq1030649 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030636
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1030636
    | exact resolve eq1030636 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030636
  have eq1030662 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030649
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1030649
    | exact resolve eq1030649 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030649
  have eq1030672 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq27 eq1030662
    | exact resolve eq1030662 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030662
  have eq1030673 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq1030672
  have eq1030681 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1030673
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1030673
    | exact resolve eq1030673 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030673
  have eq1030682 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq1030681
  have eq1030695 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq283691 eq1030682
    | exact resolve eq1030682 eq283691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283691 eq1030682
  have eq1030696 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq1030695
  have eq1030706 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have r₁ := eq1030696
       have r₂ := eq283727
       grind)
    | exact resolve eq1030696 eq283727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283727 eq1030696
  have eq1032157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq1030706 eq255057
    | exact resolve eq255057 eq1030706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030706
  have eq1032635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) := by grind
  clear eq1032157
  have eq1032664 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1032635
       have r₂ := eq28
       grind)
    | exact resolve eq1032635 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032635
  have eq1032676 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq61
       have i₂ := eq1032664
       grind)
    | exact superpose eq1032664 eq61
    | (have r₁ := eq61
       have r₂ := eq1032664
       grind)
    | exact resolve eq61 eq1032664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1032751 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5504 y
       have i₂ := eq1032664
       grind)
    | exact superpose eq1032664 eq5504
    | (have j0 := eq5504 y
       grind)
    | exact resolve eq5504 eq1032664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5504 eq1032664
  have eq1032822 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1032676
  have eq1032823 : (k x x) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1032822
  have eq1032837 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1032751
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq1032751
    | exact resolve eq1032751 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032751
  have eq1032886 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq1032837
    | exact resolve eq1032837 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032837
  have eq1032914 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1032886
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1032886
    | exact resolve eq1032886 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032886
  have eq1032941 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1032914
    | exact resolve eq1032914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032914
  have eq1032964 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1032941
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1032941
    | exact resolve eq1032941 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032941
  have eq1032965 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1032964
  have eq1032980 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1032965
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1032965
    | exact resolve eq1032965 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032965
  have eq1032986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq1032980
    | exact resolve eq1032980 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032980
  have eq1032990 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq1032986
    | exact resolve eq1032986 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032986
  have eq1032992 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1032990
       have r₂ := eq28
       grind)
    | exact resolve eq1032990 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032990
  have eq1033642 : (σ (k x x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq1032823
       grind)
    | exact superpose eq1032823 eq45
    | exact resolve eq45 eq1032823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1032823
  have eq1034032 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1033642
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1033642
    | exact resolve eq1033642 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1033642
  have eq1040592 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1034032 eq1032992
    | exact resolve eq1032992 eq1034032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032992 eq1034032
  have eq1040593 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1040592
  have eq1040604 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1040593
       have r₂ := eq255057
       grind)
    | exact resolve eq1040593 eq255057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040593
  have eq1040657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1040604 eq255057
    | exact resolve eq255057 eq1040604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255057 eq1040604
  have eq1041137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1040657
  have eq1041165 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1041137
       have r₂ := eq28
       grind)
    | exact resolve eq1041137 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041137
  have eq1041177 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1041165 eq30
    | exact resolve eq30 eq1041165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1041165
  have eq1041435 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1041177
    | exact resolve eq1041177 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1041177
  have eq1041436 : x = y := by grind
  clear eq1041435
  have eq1041440 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1041436
       grind)
    | exact superpose eq1041436 eq19
    | exact resolve eq19 eq1041436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1041441 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1041436
       grind)
    | exact superpose eq1041436 eq25
    | exact resolve eq25 eq1041436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1041436
  have eq1041860 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1041441
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1041441
    | exact resolve eq1041441 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1041441
  have eq1041861 : (M.op x y) = (k x x) := by grind
  clear eq1041440
  have eq1041862 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1041860 eq27
    | exact resolve eq27 eq1041860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1041860
  have eq1042235 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1041862
  have eq1042594 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1042235 eq52
    | exact resolve eq52 eq1042235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1042235
  have eq1042933 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1042594
       have i₂ := eq1041861
       grind)
    | exact superpose eq1041861 eq1042594
    | exact resolve eq1042594 eq1041861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041861 eq1042594
  have eq1042995 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1042933 eq15
    | exact resolve eq15 eq1042933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042933
  have eq1043693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1042995
    | exact resolve eq1042995 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1042995
  have eq1043863 : False := by grind
  exact eq1043863

/-- `x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pyx_pyy_pxx_pyx_pxx_pxx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
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
  clear eq36
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq47
  have eq52 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (M.op x y) ≠ (k x x) ∨ (k y x) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq48 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48
    | (have j0 := eq48 y x
       grind)
    | exact resolve eq48 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ y) (σ x)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq67
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq74 : (k (σ y) (σ y)) = (σ (k y y)) := by
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
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq87 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  clear eq86
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ (M.op X1 X0) = (k X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq87
  have eq96 : (M.op x y) = (k y y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq68 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq68
    | (have j0 := eq68 y x
       grind)
    | exact resolve eq68 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq68
    | (have j0 := eq68 (σ y) (σ x)
       grind)
    | exact resolve eq68 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 X0
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq48
    | (have j0 := eq48 X1 X0
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq48 X0 X0
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq68 (M.op X1 X0) (k X1 X1)
       grind)
    | exact resolve eq48 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X0) ∨ (k X1 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq107 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq108 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X0 X1) ∨ (k X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq130 : (M.op x y) ≠ (k y y) ∨ (k x x) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq88 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | (have j0 := eq88 y x
       grind)
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq88
    | (have j0 := eq88 (σ y) (σ x)
       grind)
    | exact resolve eq88 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq542 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq74
    | exact resolve eq74 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq21 eq542
    | exact resolve eq542 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq670 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq130
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq130
    | (have r₁ := eq130
       have r₂ := eq96
       grind)
    | exact resolve eq130 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq670
  have eq672 : (k x x) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq671
  have eq706 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq97 eq131
    | (have r₁ := eq131
       have r₂ := eq97
       grind)
    | exact resolve eq131 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq706
  have eq708 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq707
  have eq906 : ∀ X0 : G, (σ (k X0 x)) ≠ (k (σ x) (σ x)) ∨ (k (σ X0) (σ X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq40 eq106
    | (have j0 := eq106 (σ x) (σ X0)
       grind)
    | exact resolve eq106 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq106
  have eq911 : ∀ X0 : G, (σ (k X0 x)) ≠ (k (σ x) (σ x)) ∨ (σ (k X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq906 X0
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq906
    | (have j0 := eq906 X0
       grind)
    | (have r₁ := eq906 x
       have r₂ := eq10 x x
       grind)
    | exact resolve eq906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq960 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq108 X1 X0
       grind)
    | exact superpose eq108 eq48
    | (have j0 := eq48 X0 X1
       have j1 := eq108 X1 X0
       grind)
    | (have r₁ := eq48 X1 X1
       have r₂ := eq108 X1 X1
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq108 (M.op X1 X0) (k X1 X1)
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq108 (k X1 X1) (M.op X1 X0)
       grind)
    | exact resolve eq48 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq108
  have eq966 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq960 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq20696 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq543 eq97
    | exact resolve eq97 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq20729 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq20696
       have r₂ := eq28
       grind)
    | exact resolve eq20696 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20696
  have eq20756 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq20729 eq80
    | exact resolve eq80 eq20729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20729
  have eq21066 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq20756
       have i₂ := eq672
       grind)
    | exact superpose eq672 eq20756
    | exact resolve eq20756 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20756
  have eq21085 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq21066
  have eq21709 : (k (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq21085
       grind)
    | exact superpose eq21085 eq44
    | exact resolve eq44 eq21085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21085
  have eq21770 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq21709
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq21709
    | exact resolve eq21709 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21709
  have eq21771 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq21770
  have eq21804 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq21771 eq62
    | (have r₁ := eq62
       have r₂ := eq21771
       grind)
    | exact resolve eq62 eq21771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21771
  have eq21828 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq21804
  have eq21829 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq21828
  have eq22171 : (k y y) = (τ (k (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq21829 eq85
    | exact resolve eq85 eq21829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21829
  have eq22210 : (k y x) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq80 eq22171
    | exact resolve eq22171 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22171
  have eq22213 : (k y x) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq22210
       have r₂ := eq61
       grind)
    | exact resolve eq22210 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22210
  have eq22461 : (k (σ y) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq22213
       grind)
    | exact superpose eq22213 eq74
    | exact resolve eq74 eq22213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22464 : (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq22213
       grind)
    | exact superpose eq22213 eq96
    | exact resolve eq96 eq22213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq22213
  have eq22492 : (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq22464
  have eq22507 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq22461
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq22461
    | exact resolve eq22461 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22461
  have eq22531 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq22492
       grind)
    | exact superpose eq22492 eq73
    | exact resolve eq73 eq22492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq22559 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq22531
    | exact resolve eq22531 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22531
  have eq22840 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22559 eq708
    | exact resolve eq708 eq22559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22559
  have eq22848 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq22840
  have eq22854 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq22848
       have r₂ := eq28
       grind)
    | exact resolve eq22848 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22848
  have eq22871 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq22507 eq97
    | exact resolve eq97 eq22507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq22872 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq22507 eq131
    | exact resolve eq131 eq22507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq22507
  have eq22898 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq22872
  have eq22899 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq22871
  have eq22908 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq22898
       have r₂ := eq708
       grind)
    | exact resolve eq22898 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708 eq22898
  have eq25132 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq22854 eq62
    | (have r₁ := eq62
       have r₂ := eq22854
       grind)
    | exact resolve eq62 eq22854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq22854
  have eq25159 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq25132
  have eq25160 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq25159
  have eq40533 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq22908 eq22899
    | exact resolve eq22899 eq22908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22899 eq22908
  have eq40570 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq40533
  have eq51432 : (k y y) = (τ (k (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq25160 eq85
    | exact resolve eq85 eq25160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq25160
  have eq51471 : (k y x) = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq80 eq51432
    | exact resolve eq51432 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq51432
  have eq51474 : (k y x) = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq51471
       have r₂ := eq61
       grind)
    | exact resolve eq51471 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq51471
  have eq51773 : (M.op x y) ≠ (k y x) ∨ (k x x) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq130
       have i₂ := eq51474
       grind)
    | exact superpose eq51474 eq130
    | exact resolve eq130 eq51474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq51474
  have eq51798 : (M.op x y) ≠ (k y x) ∨ (k x x) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq51773
  have eq51811 : (k x x) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq51798
       have r₂ := eq672
       grind)
    | exact resolve eq51798 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq51798
  have eq54116 : (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq22492
       have i₂ := eq51811
       grind)
    | exact superpose eq51811 eq22492
    | exact resolve eq22492 eq51811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22492 eq51811
  have eq54170 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by grind
  clear eq54116
  have eq54220 : (τ (σ (M.op x y))) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq54170 eq52
    | exact resolve eq52 eq54170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54170
  have eq54315 : (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq31 eq54220
    | exact resolve eq54220 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq54220
  have eq54316 : (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq54315
  have eq54324 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq54316
       grind)
    | exact superpose eq54316 eq44
    | exact resolve eq44 eq54316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq54411 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq54324
    | exact resolve eq54324 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54324
  have eq54449 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq54411 eq40570
    | exact resolve eq40570 eq54411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40570
  have eq54517 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq54449
  have eq54527 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq54517
       have r₂ := eq28
       grind)
    | exact resolve eq54517 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54517
  have eq54830 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (k y y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq911 y
       have i₂ := eq54527
       grind)
    | exact superpose eq54527 eq911
    | (have j0 := eq911 y
       grind)
    | exact resolve eq911 eq54527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq54833 : (M.op x y) ≠ (k x x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq966 y x
       have i₂ := eq54527
       grind)
    | exact superpose eq54527 eq966
    | (have j0 := eq966 (M.op x y) (k y y)
       grind)
    | exact resolve eq966 eq54527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq54527
  have eq54834 : (M.op x y) ≠ (k x x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq54833
  have eq54845 : (M.op x y) = (k y y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq54834
       have r₂ := eq54316
       grind)
    | exact resolve eq54834 eq54316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54316 eq54834
  have eq54847 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (k y y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq54830
    | exact resolve eq54830 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54830
  have eq54857 : (M.op x y) = (k y y) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54845
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54845
    | exact resolve eq54845 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54845
  have eq54858 : (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq54857
  have eq54860 : (σ (k y y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq54847
       have r₂ := eq54411
       grind)
    | exact resolve eq54847 eq54411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54411 eq54847
  have eq54862 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54860
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq54860
    | exact resolve eq54860 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54860
  have eq54864 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54862
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq54862
    | exact resolve eq54862 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54862
  have eq54866 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq54864
    | exact resolve eq54864 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54864
  have eq54868 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54866
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq54866
    | exact resolve eq54866 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54866
  have eq54869 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq54868
  have eq54871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq54869
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq54869
    | exact resolve eq54869 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54869
  have eq54873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq54871
    | exact resolve eq54871 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54871
  have eq54876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq54873
    | exact resolve eq54873 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54873
  have eq54878 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq54876
       have r₂ := eq28
       grind)
    | exact resolve eq54876 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54876
  have eq55186 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq54858
       grind)
    | exact superpose eq54858 eq74
    | exact resolve eq74 eq54858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq54858
  have eq55261 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq55186
    | exact resolve eq55186 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55186
  have eq55639 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq55261 eq54878
    | exact resolve eq54878 eq55261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54878 eq55261
  have eq55657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq55639
  have eq55684 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq55657
       have r₂ := eq28
       grind)
    | exact resolve eq55657 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55657
  have eq55698 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq55684 eq30
    | exact resolve eq30 eq55684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq55684
  have eq55819 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq55698
    | exact resolve eq55698 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq55698
  have eq55820 : x = y := by grind
  clear eq55819
  have eq56081 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq55820
       grind)
    | exact superpose eq55820 eq19
    | exact resolve eq19 eq55820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq56082 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq55820
       grind)
    | exact superpose eq55820 eq25
    | exact resolve eq25 eq55820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq55820
  have eq56302 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq56082
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq56082
    | exact resolve eq56082 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq56082
  have eq56303 : (M.op x y) = (k x x) := by grind
  clear eq56081
  have eq56304 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq56302 eq27
    | exact resolve eq27 eq56302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq56302
  have eq56426 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq56304
  have eq56534 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq56426 eq52
    | exact resolve eq52 eq56426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq56426
  have eq56569 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq56534
       have i₂ := eq56303
       grind)
    | exact superpose eq56303 eq56534
    | exact resolve eq56534 eq56303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56303 eq56534
  have eq56585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56569 eq15
    | exact resolve eq15 eq56569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56569
  have eq56794 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq56585
    | exact resolve eq56585 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq56585
  have eq56857 : False := by grind
  exact eq56857
