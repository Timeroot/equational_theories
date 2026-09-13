import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if X = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pyy_x_pxx_y_pyx_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq22 : ∀ X1 : G, (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  have eq23 : ∀ X1 : G, (k (k X1 X1) X1) = (M.op X1 (k X1 X1)) ∨ (k X1 X1) = X1 := by
    intro X1
    grind
  clear eq22
  have eq28 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
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
  have eq29 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq28
    | (have j0 := eq28 X0
       grind)
    | exact resolve eq28 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X1) = X0 ∨ X0 = X1 ∨ (k X0 X0) = X1 := by
    intro X0 X1
    grind
  clear eq38
  have eq48 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
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
  have eq50 : (σ x) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
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
  have eq51 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
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
  have eq64 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq65 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  clear eq64
  have eq66 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  clear eq65
  have eq67 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    grind
  clear eq66
  have eq82 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k X0 X0)
       have i₂ := eq67 X0
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
  have eq83 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq82 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (k x x) := by
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
  have eq89 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by grind
  clear eq88
  have eq102 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
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
  have eq107 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq15 X0 (k X0 X0)
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
  have eq1463 : x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq23 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq23
    | exact resolve eq23 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1464 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
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
  have eq1474 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq1464
  have eq8787 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
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
  have eq8788 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq8787
  have eq8789 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq8788
  have eq8790 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have r₁ := eq8789
       have r₂ := eq15 x x
       grind)
    | exact resolve eq8789 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8789
  have eq9662 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
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
  have eq24485 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq9662
       have i₂ := eq8790
       grind)
    | exact superpose eq8790 eq9662
    | exact resolve eq9662 eq8790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8790 eq9662
  have eq24488 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24485
  have eq24489 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24488
  have eq24496 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq24489
       grind)
    | exact superpose eq24489 eq83
    | exact resolve eq83 eq24489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24499 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq24489
       grind)
    | exact superpose eq24489 eq107
    | exact resolve eq107 eq24489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24489
  have eq24512 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24499
  have eq24535 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24512
       grind)
    | exact superpose eq24512 eq16
    | exact resolve eq16 eq24512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24512
  have eq24551 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq24535
       have i₂ := eq24496
       grind)
    | exact superpose eq24496 eq24535
    | exact resolve eq24535 eq24496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24496 eq24535
  have eq24556 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = y := by grind
  clear eq24551
  have eq24557 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24556
  have eq24560 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24557
       grind)
    | exact superpose eq24557 eq16
    | exact resolve eq16 eq24557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24557
  have eq24561 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24560
  have eq24562 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24561
  have eq24563 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq24562
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24562 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24562
  have eq24567 : y = (τ (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq24563
       grind)
    | exact superpose eq24563 eq9
    | exact resolve eq9 eq24563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24563
  have eq24828 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq24567
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq24567
    | exact resolve eq24567 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24567
  have eq24841 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24828
       grind)
    | exact superpose eq24828 eq16
    | exact resolve eq16 eq24828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24828
  have eq24842 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24841
  have eq24843 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24842
  have eq24844 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq24843
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24843 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24843
  have eq24858 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq24844
       grind)
    | exact superpose eq24844 eq9
    | exact resolve eq9 eq24844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24844
  have eq25116 : y = (k x x) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq24858
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq24858
    | exact resolve eq24858 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24858
  have eq25127 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq23 x
       have i₂ := eq25116
       grind)
    | exact superpose eq25116 eq23
    | exact resolve eq23 eq25116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq25128 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq25116
       grind)
    | exact superpose eq25116 eq29
    | exact resolve eq29 eq25116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25116
  have eq30702 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25128
       grind)
    | exact superpose eq25128 eq16
    | exact resolve eq16 eq25128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25128
  have eq30718 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq30702
       have i₂ := eq25127
       grind)
    | exact superpose eq25127 eq30702
    | exact resolve eq30702 eq25127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25127 eq30702
  have eq30732 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq30718
  have eq30733 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30732
  have eq30740 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30733
       grind)
    | exact superpose eq30733 eq16
    | exact resolve eq16 eq30733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30733
  have eq30754 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30740
  have eq30755 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30754
  have eq30756 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq30755
       have r₂ := eq15 x x
       grind)
    | exact resolve eq30755 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30755
  have eq30760 : y = (τ (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq30756
       grind)
    | exact superpose eq30756 eq9
    | exact resolve eq9 eq30756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30756
  have eq31029 : x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq30760
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq30760
    | exact resolve eq30760 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30760
  have eq31042 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31029
       grind)
    | exact superpose eq31029 eq16
    | exact resolve eq16 eq31029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31029
  have eq31056 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq31042
  have eq31057 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq31056
  have eq31058 : (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq31057
       have r₂ := eq15 x x
       grind)
    | exact resolve eq31057 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31057
  have eq31078 : (k y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq31058
       grind)
    | exact superpose eq31058 eq9
    | exact resolve eq9 eq31058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31058
  have eq31344 : x = (k y y) := by
    first
    | (have i₁ := eq31078
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq31078
    | exact resolve eq31078 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31078
  have eq31383 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq31344
       grind)
    | exact superpose eq31344 eq83
    | exact resolve eq83 eq31344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq31386 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq31344
       grind)
    | exact superpose eq31344 eq107
    | exact resolve eq107 eq31344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq31344
  have eq31452 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31386
       grind)
    | exact superpose eq31386 eq16
    | exact resolve eq16 eq31386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31386
  have eq31470 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31452
       have i₂ := eq31383
       grind)
    | exact superpose eq31383 eq31452
    | exact resolve eq31452 eq31383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31383 eq31452
  have eq31472 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq31470
  have eq31485 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31472
       grind)
    | exact superpose eq31472 eq16
    | exact resolve eq16 eq31472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31472
  have eq31501 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq31485
  have eq31502 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq31501
  have eq31503 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq31502
       have r₂ := eq15 x x
       grind)
    | exact resolve eq31502 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31502
  have eq31506 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq31503
       grind)
    | exact superpose eq31503 eq9
    | exact resolve eq9 eq31503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31503
  have eq31780 : x = y := by
    first
    | (have i₁ := eq31506
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq31506
    | exact resolve eq31506 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31506
  have eq31852 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31780
       grind)
    | exact superpose eq31780 eq16
    | exact resolve eq16 eq31780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31780
  have eq31868 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) := by grind
  clear eq31852
  have eq31869 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq31868
  have eq31870 : False := by grind
  exact eq31870

/-- `x □ y = if X = Y then m(Y,Y) else if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pyy_x_pxx_y_pyy_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq22 : ∀ X1 : G, (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq23 : ∀ X1 : G, (k (k X1 X1) X1) = (M.op (k X1 X1) X1) ∨ (k X1 X1) = X1 := by
    intro X1
    grind
  clear eq22
  have eq28 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
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
  have eq29 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq28
    | (have j0 := eq28 X0
       grind)
    | exact resolve eq28 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X1) = X0 ∨ X0 = X1 ∨ (k X0 X0) = X1 := by
    intro X0 X1
    grind
  clear eq38
  have eq48 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
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
  have eq49 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
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
  have eq50 : (σ y) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
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
  have eq51 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
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
  have eq64 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq65 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq64
  have eq66 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  clear eq65
  have eq67 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    grind
  clear eq66
  have eq82 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k X0 X0)
       have i₂ := eq67 X0
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
  have eq83 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq82 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ x = (k y y) := by
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
  have eq89 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq88
  have eq102 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
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
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq15 X0 (k X0 X0)
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
  have eq1468 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq83 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq83
    | exact resolve eq83 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1470 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
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
  have eq1473 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq1470
  have eq9085 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
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
  have eq24339 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq9085
       have i₂ := eq1468
       grind)
    | exact superpose eq1468 eq9085
    | exact resolve eq9085 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468 eq9085
  have eq24342 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ x = y := by grind
  clear eq24339
  have eq24343 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq24342
  have eq24344 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24343
       grind)
    | exact superpose eq24343 eq16
    | exact resolve eq16 eq24343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24343
  have eq24345 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq24344
  have eq24346 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq24345
  have eq24347 : x = (k y y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq24346
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24346 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24346
  have eq24471 : (M.op x y) = (k x y) ∨ x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23 y
       have i₂ := eq24347
       grind)
    | exact superpose eq24347 eq23
    | exact resolve eq23 eq24347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24472 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24347
       grind)
    | exact superpose eq24347 eq29
    | exact resolve eq29 eq24347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24347
  have eq24493 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24472
  have eq24805 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24493
       grind)
    | exact superpose eq24493 eq16
    | exact resolve eq16 eq24493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24493
  have eq24813 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24805
       have i₂ := eq24471
       grind)
    | exact superpose eq24471 eq24805
    | exact resolve eq24805 eq24471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24471 eq24805
  have eq24818 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq24813
  have eq24819 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24818
  have eq24822 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24819
       grind)
    | exact superpose eq24819 eq16
    | exact resolve eq16 eq24819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24819
  have eq24823 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24822
  have eq24824 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24823
  have eq24825 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq24824
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24824 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24824
  have eq24839 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq24825
       grind)
    | exact superpose eq24825 eq9
    | exact resolve eq9 eq24825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24825
  have eq25100 : y = (k x x) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24839
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq24839
    | exact resolve eq24839 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24839
  have eq25115 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq83 x
       have i₂ := eq25100
       grind)
    | exact superpose eq25100 eq83
    | exact resolve eq83 eq25100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq25118 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq107 x
       have i₂ := eq25100
       grind)
    | exact superpose eq25100 eq107
    | exact resolve eq107 eq25100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq25100
  have eq25131 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq25118
  have eq25157 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25131
       grind)
    | exact superpose eq25131 eq16
    | exact resolve eq16 eq25131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25131
  have eq25167 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25157
       have i₂ := eq25115
       grind)
    | exact superpose eq25115 eq25157
    | exact resolve eq25157 eq25115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25115 eq25157
  have eq25175 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq25167
  have eq25176 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25175
  have eq25179 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25176
       grind)
    | exact superpose eq25176 eq16
    | exact resolve eq16 eq25176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25176
  have eq25180 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25179
  have eq25181 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25180
  have eq25182 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq25181
       have r₂ := eq15 x x
       grind)
    | exact resolve eq25181 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25181
  have eq25186 : y = (τ (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq25182
       grind)
    | exact superpose eq25182 eq9
    | exact resolve eq9 eq25182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25182
  have eq25447 : x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq25186
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq25186
    | exact resolve eq25186 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25186
  have eq25460 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25447
       grind)
    | exact superpose eq25447 eq16
    | exact resolve eq16 eq25447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25447
  have eq25461 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq25460
  have eq25462 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq25461
  have eq25463 : (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq25462
       have r₂ := eq15 x x
       grind)
    | exact resolve eq25462 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25462
  have eq25482 : (k y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq25463
       grind)
    | exact superpose eq25463 eq9
    | exact resolve eq9 eq25463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25463
  have eq25740 : x = (k y y) := by
    first
    | (have i₁ := eq25482
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq25482
    | exact resolve eq25482 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25482
  have eq25774 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq23 y
       have i₂ := eq25740
       grind)
    | exact superpose eq25740 eq23
    | exact resolve eq23 eq25740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq25775 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq25740
       grind)
    | exact superpose eq25740 eq29
    | exact resolve eq29 eq25740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25740
  have eq25828 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25775
       grind)
    | exact superpose eq25775 eq16
    | exact resolve eq16 eq25775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25775
  have eq25838 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25828
       have i₂ := eq25774
       grind)
    | exact superpose eq25774 eq25828
    | exact resolve eq25828 eq25774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25774 eq25828
  have eq25849 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq25838
  have eq25850 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25849
       grind)
    | exact superpose eq25849 eq16
    | exact resolve eq16 eq25849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25849
  have eq25853 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq25850
  have eq25854 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq25853
  have eq25855 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq25854
       have r₂ := eq15 x x
       grind)
    | exact resolve eq25854 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25854
  have eq25857 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq25855
       grind)
    | exact superpose eq25855 eq9
    | exact resolve eq9 eq25855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25855
  have eq26123 : x = y := by
    first
    | (have i₁ := eq25857
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq25857
    | exact resolve eq25857 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25857
  have eq26194 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26123
       grind)
    | exact superpose eq26123 eq16
    | exact resolve eq16 eq26123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26123
  have eq26197 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) := by grind
  clear eq26194
  have eq26198 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq26197
  have eq26199 : False := by grind
  exact eq26199

/-- `x □ y = if X = Y then m(Y,Y) else if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pyy_x_pxx_y_pyy_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq22 : ∀ X1 : G, (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  have eq23 : ∀ X1 : G, (k (k X1 X1) X1) = (M.op X1 (k X1 X1)) ∨ (k X1 X1) = X1 := by
    intro X1
    grind
  clear eq22
  have eq28 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
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
  have eq29 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq28
    | (have j0 := eq28 X0
       grind)
    | exact resolve eq28 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X1) = X0 ∨ X0 = X1 ∨ (k X0 X0) = X1 := by
    intro X0 X1
    grind
  clear eq38
  have eq48 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
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
  have eq50 : (σ x) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
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
  have eq51 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
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
  have eq64 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq65 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  clear eq64
  have eq66 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  clear eq65
  have eq67 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    grind
  clear eq66
  have eq82 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k X0 X0)
       have i₂ := eq67 X0
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
  have eq83 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq82 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (k x x) := by
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
  have eq89 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by grind
  clear eq88
  have eq102 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
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
  have eq107 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq15 X0 (k X0 X0)
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
  have eq1463 : x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq23 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq23
    | exact resolve eq23 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1464 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
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
  have eq1474 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq1464
  have eq8787 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
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
  have eq8788 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq8787
  have eq8789 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq8788
  have eq8790 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have r₁ := eq8789
       have r₂ := eq15 x x
       grind)
    | exact resolve eq8789 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8789
  have eq9662 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
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
  have eq24485 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq9662
       have i₂ := eq8790
       grind)
    | exact superpose eq8790 eq9662
    | exact resolve eq9662 eq8790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8790 eq9662
  have eq24488 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24485
  have eq24489 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24488
  have eq24496 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq24489
       grind)
    | exact superpose eq24489 eq83
    | exact resolve eq83 eq24489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24499 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq24489
       grind)
    | exact superpose eq24489 eq107
    | exact resolve eq107 eq24489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24489
  have eq24512 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24499
  have eq24535 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24512
       grind)
    | exact superpose eq24512 eq16
    | exact resolve eq16 eq24512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24512
  have eq24551 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq24535
       have i₂ := eq24496
       grind)
    | exact superpose eq24496 eq24535
    | exact resolve eq24535 eq24496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24496 eq24535
  have eq24556 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = y := by grind
  clear eq24551
  have eq24557 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24556
  have eq24560 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24557
       grind)
    | exact superpose eq24557 eq16
    | exact resolve eq16 eq24557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24557
  have eq24561 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24560
  have eq24562 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24561
  have eq24563 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq24562
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24562 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24562
  have eq24567 : y = (τ (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq24563
       grind)
    | exact superpose eq24563 eq9
    | exact resolve eq9 eq24563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24563
  have eq24828 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq24567
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq24567
    | exact resolve eq24567 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24567
  have eq24841 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24828
       grind)
    | exact superpose eq24828 eq16
    | exact resolve eq16 eq24828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24828
  have eq24842 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24841
  have eq24843 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24842
  have eq24844 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq24843
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24843 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24843
  have eq24858 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq24844
       grind)
    | exact superpose eq24844 eq9
    | exact resolve eq9 eq24844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24844
  have eq25116 : y = (k x x) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq24858
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq24858
    | exact resolve eq24858 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24858
  have eq25127 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq23 x
       have i₂ := eq25116
       grind)
    | exact superpose eq25116 eq23
    | exact resolve eq23 eq25116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq25128 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq25116
       grind)
    | exact superpose eq25116 eq29
    | exact resolve eq29 eq25116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25116
  have eq30702 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25128
       grind)
    | exact superpose eq25128 eq16
    | exact resolve eq16 eq25128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25128
  have eq30718 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq30702
       have i₂ := eq25127
       grind)
    | exact superpose eq25127 eq30702
    | exact resolve eq30702 eq25127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25127 eq30702
  have eq30732 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq30718
  have eq30733 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30732
  have eq30740 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30733
       grind)
    | exact superpose eq30733 eq16
    | exact resolve eq16 eq30733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30733
  have eq30754 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30740
  have eq30755 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30754
  have eq30756 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq30755
       have r₂ := eq15 x x
       grind)
    | exact resolve eq30755 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30755
  have eq30760 : y = (τ (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq30756
       grind)
    | exact superpose eq30756 eq9
    | exact resolve eq9 eq30756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30756
  have eq31029 : x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq30760
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq30760
    | exact resolve eq30760 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30760
  have eq31042 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31029
       grind)
    | exact superpose eq31029 eq16
    | exact resolve eq16 eq31029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31029
  have eq31056 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq31042
  have eq31057 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq31056
  have eq31058 : (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq31057
       have r₂ := eq15 x x
       grind)
    | exact resolve eq31057 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31057
  have eq31078 : (k y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq31058
       grind)
    | exact superpose eq31058 eq9
    | exact resolve eq9 eq31058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31058
  have eq31344 : x = (k y y) := by
    first
    | (have i₁ := eq31078
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq31078
    | exact resolve eq31078 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31078
  have eq31383 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq31344
       grind)
    | exact superpose eq31344 eq83
    | exact resolve eq83 eq31344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq31386 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq31344
       grind)
    | exact superpose eq31344 eq107
    | exact resolve eq107 eq31344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq31344
  have eq31452 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31386
       grind)
    | exact superpose eq31386 eq16
    | exact resolve eq16 eq31386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31386
  have eq31470 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31452
       have i₂ := eq31383
       grind)
    | exact superpose eq31383 eq31452
    | exact resolve eq31452 eq31383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31383 eq31452
  have eq31472 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq31470
  have eq31485 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31472
       grind)
    | exact superpose eq31472 eq16
    | exact resolve eq16 eq31472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31472
  have eq31501 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq31485
  have eq31502 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq31501
  have eq31503 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq31502
       have r₂ := eq15 x x
       grind)
    | exact resolve eq31502 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31502
  have eq31506 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq31503
       grind)
    | exact superpose eq31503 eq9
    | exact resolve eq9 eq31503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31503
  have eq31780 : x = y := by
    first
    | (have i₁ := eq31506
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq31506
    | exact resolve eq31506 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31506
  have eq31852 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31780
       grind)
    | exact superpose eq31780 eq16
    | exact resolve eq16 eq31780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31780
  have eq31868 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) := by grind
  clear eq31852
  have eq31869 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq31868
  have eq31870 : False := by grind
  exact eq31870
