import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq33 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ X1 = X2 ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq12 X1 X2
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2
       have i₂ := eq12 X0 X2
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X1 X1 X2
       have j1 := eq39 X1 X1 X2
       grind)
    | (have r₁ := eq33 X0 X1 X2
       have r₂ := eq39 X0 X1 X2
       grind)
    | (have r₁ := eq33 X1 X0 X2
       have r₂ := eq39 X0 X1 X2
       grind)
    | (have r₁ := eq33 X0 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq39 X0 X1 X2
       grind)
    | exact resolve eq33 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq39
  have eq100 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq101 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq186 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq102 (σ X0) (σ X1)
       grind)
    | exact superpose eq102 eq13
    | (have j1 := eq102 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq102 (τ X0) X1
       grind)
    | exact superpose eq102 eq16
    | (have j1 := eq102 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq16 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq102
  have eq456 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq188 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq188
    | exact resolve eq188 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq481 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq456
    | (have j0 := eq456 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq456 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq1473 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq186 x y
       grind)
    | exact superpose eq186 eq14
    | (have j1 := eq186 x y
       grind)
    | exact resolve eq14 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1564 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1473
       have i₂ := eq481 x y
       grind)
    | exact superpose eq481 eq1473
    | (have j1 := eq481 (σ x) (σ y)
       grind)
    | (have r₁ := eq1473
       have r₂ := eq481 x y
       grind)
    | (have r₁ := eq1473
       have r₂ := eq481 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1473
       have r₂ := eq481 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1473 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481 eq1473
  have eq1565 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1564
  have eq1643 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1565
       grind)
    | exact superpose eq1565 eq8
    | exact resolve eq8 eq1565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq1687 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1643
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1643
    | exact resolve eq1643 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq1688 : x = y := by grind
  clear eq1687
  have eq1762 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1688
       grind)
    | exact superpose eq1688 eq14
    | exact resolve eq14 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688
  have eq1763 : False := by grind
  exact eq1763

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq35 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq37 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq35
    | (have j0 := eq35 X0 X1
       grind)
    | exact resolve eq35 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq43 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq61 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq80 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq86 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq43 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq8
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq8 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq186 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq175
    | (have j0 := eq175 X0 X1
       grind)
    | exact resolve eq175 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1032 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1172 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq186 x y
       grind)
    | exact superpose eq186 eq14
    | (have j1 := eq186 x y
       grind)
    | exact resolve eq14 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1346 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq36
    | exact resolve eq36 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1493 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1346 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1346
    | (have j0 := eq1346 X0 X1
       grind)
    | exact resolve eq1346 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1877 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1 (σ X0)
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq86
    | (have j0 := eq86 X1 (σ X0)
       grind)
    | (have r₁ := eq86 X0 (σ X0)
       have r₂ := eq27 X0
       grind)
    | exact resolve eq86 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1906 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1877 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1877
    | (have j0 := eq1877 X0 X1
       grind)
    | exact resolve eq1877 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq23011 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1172
       have i₂ := eq1493 y x
       grind)
    | exact superpose eq1493 eq1172
    | (have j1 := eq1493 x y
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 y x
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1172 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172 eq1493
  have eq23012 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23011
  have eq23013 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23012
  have eq23073 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq23013
       grind)
    | exact superpose eq23013 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq23013
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq23013
       grind)
    | exact resolve eq10 eq23013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23107 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1906 y X0
       have i₂ := eq23013
       grind)
    | exact superpose eq23013 eq1906
    | (have j0 := eq1906 X0 x
       grind)
    | exact resolve eq1906 eq23013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906 eq23013
  have eq29089 : (k y x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq23073 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23073
  have eq29185 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq61 x y
       have i₂ := eq29089
       grind)
    | exact superpose eq29089 eq61
    | (have j0 := eq61 x y
       grind)
    | exact resolve eq61 eq29089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq29089
  have eq29194 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq29185
  have eq29200 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq1032 x y
       grind)
    | (have r₁ := eq29194
       have r₂ := eq1032 x y
       grind)
    | (have r₁ := eq29194
       have r₂ := eq1032 y x
       grind)
    | exact resolve eq29194 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032 eq29194
  have eq69869 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq23107 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23107
  have eq69876 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq69869
       grind)
    | exact superpose eq69869 eq14
    | exact resolve eq14 eq69869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69869
  have eq69896 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq69876
       have i₂ := eq29200
       grind)
    | exact superpose eq29200 eq69876
    | exact resolve eq69876 eq29200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29200 eq69876
  have eq69915 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq69896
  have eq69916 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq69915
  have eq69922 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq69916
       grind)
    | exact superpose eq69916 eq8
    | exact resolve eq8 eq69916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69916
  have eq70265 : x = y ∨ x = y := by
    first
    | (have i₁ := eq69922
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq69922
    | exact resolve eq69922 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69922
  have eq70266 : x = y := by grind
  clear eq70265
  have eq70272 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq70266
       grind)
    | exact superpose eq70266 eq14
    | exact resolve eq14 eq70266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70266
  have eq70273 : False := by grind
  exact eq70273

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq35 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq37 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq35
    | (have j0 := eq35 X0 X1
       grind)
    | exact resolve eq35 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq43 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq61 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq80 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq86 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq43 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq8
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq8 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq186 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq175
    | (have j0 := eq175 X0 X1
       grind)
    | exact resolve eq175 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1032 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1172 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq186 x y
       grind)
    | exact superpose eq186 eq14
    | (have j1 := eq186 x y
       grind)
    | exact resolve eq14 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1346 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq36
    | exact resolve eq36 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1493 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1346 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1346
    | (have j0 := eq1346 X0 X1
       grind)
    | exact resolve eq1346 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1877 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1 (σ X0)
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq86
    | (have j0 := eq86 X1 (σ X0)
       grind)
    | (have r₁ := eq86 X0 (σ X0)
       have r₂ := eq27 X0
       grind)
    | exact resolve eq86 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1906 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1877 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1877
    | (have j0 := eq1877 X0 X1
       grind)
    | exact resolve eq1877 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq20106 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1172
       have i₂ := eq1493 y x
       grind)
    | exact superpose eq1493 eq1172
    | (have j1 := eq1493 x y
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 y x
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1172 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172 eq1493
  have eq20107 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20106
  have eq20108 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20107
  have eq20162 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq20108
       grind)
    | exact superpose eq20108 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq20108
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq20108
       grind)
    | exact resolve eq10 eq20108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20190 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1906 y X0
       have i₂ := eq20108
       grind)
    | exact superpose eq20108 eq1906
    | (have j0 := eq1906 X0 x
       grind)
    | exact resolve eq1906 eq20108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906 eq20108
  have eq26152 : (k y x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq20162 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20162
  have eq26248 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq61 x y
       have i₂ := eq26152
       grind)
    | exact superpose eq26152 eq61
    | (have j0 := eq61 x y
       grind)
    | exact resolve eq61 eq26152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq26152
  have eq26257 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq26248
  have eq26263 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq1032 x y
       grind)
    | (have r₁ := eq26257
       have r₂ := eq1032 x y
       grind)
    | (have r₁ := eq26257
       have r₂ := eq1032 y x
       grind)
    | exact resolve eq26257 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032 eq26257
  have eq66590 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq20190 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20190
  have eq66597 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq66590
       grind)
    | exact superpose eq66590 eq14
    | exact resolve eq14 eq66590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66590
  have eq66617 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq66597
       have i₂ := eq26263
       grind)
    | exact superpose eq26263 eq66597
    | exact resolve eq66597 eq26263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26263 eq66597
  have eq66636 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq66617
  have eq66637 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq66636
  have eq66643 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq66637
       grind)
    | exact superpose eq66637 eq8
    | exact resolve eq8 eq66637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66637
  have eq66986 : x = y ∨ x = y := by
    first
    | (have i₁ := eq66643
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq66643
    | exact resolve eq66643 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66643
  have eq66987 : x = y := by grind
  clear eq66986
  have eq66993 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq66987
       grind)
    | exact superpose eq66987 eq14
    | exact resolve eq14 eq66987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66987
  have eq66994 : False := by grind
  exact eq66994

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq33 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ X1 = X2 ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq12 X1 X2
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2
       have i₂ := eq12 X0 X2
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X1 X1 X2
       have j1 := eq39 X1 X1 X2
       grind)
    | (have r₁ := eq33 X0 X1 X2
       have r₂ := eq39 X0 X1 X2
       grind)
    | (have r₁ := eq33 X1 X0 X2
       have r₂ := eq39 X0 X1 X2
       grind)
    | (have r₁ := eq33 X0 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq39 X0 X1 X2
       grind)
    | exact resolve eq33 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq39
  have eq100 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq101 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq186 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq102 (σ X0) (σ X1)
       grind)
    | exact superpose eq102 eq13
    | (have j1 := eq102 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq102 (τ X0) X1
       grind)
    | exact superpose eq102 eq16
    | (have j1 := eq102 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq16 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq102
  have eq456 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq188 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq188
    | exact resolve eq188 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq481 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq456
    | (have j0 := eq456 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq456 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq1473 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq186 x y
       grind)
    | exact superpose eq186 eq14
    | (have j1 := eq186 x y
       grind)
    | exact resolve eq14 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1564 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1473
       have i₂ := eq481 x y
       grind)
    | exact superpose eq481 eq1473
    | (have j1 := eq481 (σ x) (σ y)
       grind)
    | (have r₁ := eq1473
       have r₂ := eq481 x y
       grind)
    | (have r₁ := eq1473
       have r₂ := eq481 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1473
       have r₂ := eq481 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1473 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481 eq1473
  have eq1565 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1564
  have eq1643 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1565
       grind)
    | exact superpose eq1565 eq8
    | exact resolve eq8 eq1565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq1687 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1643
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1643
    | exact resolve eq1643 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq1688 : x = y := by grind
  clear eq1687
  have eq1762 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1688
       grind)
    | exact superpose eq1688 eq14
    | exact resolve eq14 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688
  have eq1763 : False := by grind
  exact eq1763

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq35 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq37 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X2 X0) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq35
    | (have j0 := eq35 X0 X1
       grind)
    | exact resolve eq35 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq43 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq61 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq80 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq86 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq43 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq8
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq8 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq186 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq175
    | (have j0 := eq175 X0 X1
       grind)
    | exact resolve eq175 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1032 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1172 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq186 x y
       grind)
    | exact superpose eq186 eq14
    | (have j1 := eq186 x y
       grind)
    | exact resolve eq14 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1346 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq36
    | exact resolve eq36 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1493 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1346 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1346
    | (have j0 := eq1346 X0 X1
       grind)
    | exact resolve eq1346 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1877 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1 (σ X0)
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq86
    | (have j0 := eq86 X1 (σ X0)
       grind)
    | (have r₁ := eq86 X0 (σ X0)
       have r₂ := eq27 X0
       grind)
    | exact resolve eq86 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1906 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1877 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1877
    | (have j0 := eq1877 X0 X1
       grind)
    | exact resolve eq1877 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq23787 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1172
       have i₂ := eq1493 y x
       grind)
    | exact superpose eq1493 eq1172
    | (have j1 := eq1493 x y
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 y x
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1172 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172 eq1493
  have eq23788 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23787
  have eq23789 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23788
  have eq23849 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq23789
       grind)
    | exact superpose eq23789 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq23789
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq23789
       grind)
    | exact resolve eq10 eq23789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23883 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1906 y X0
       have i₂ := eq23789
       grind)
    | exact superpose eq23789 eq1906
    | (have j0 := eq1906 X0 x
       grind)
    | exact resolve eq1906 eq23789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906 eq23789
  have eq29883 : (k y x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq23849 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23849
  have eq29979 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq61 x y
       have i₂ := eq29883
       grind)
    | exact superpose eq29883 eq61
    | (have j0 := eq61 x y
       grind)
    | exact resolve eq61 eq29883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq29883
  have eq29988 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq29979
  have eq29994 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq1032 x y
       grind)
    | (have r₁ := eq29988
       have r₂ := eq1032 x y
       grind)
    | (have r₁ := eq29988
       have r₂ := eq1032 y x
       grind)
    | exact resolve eq29988 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032 eq29988
  have eq70791 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq23883 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23883
  have eq70801 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq70791
       grind)
    | exact superpose eq70791 eq14
    | exact resolve eq14 eq70791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70791
  have eq70821 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70801
       have i₂ := eq29994
       grind)
    | exact superpose eq29994 eq70801
    | exact resolve eq70801 eq29994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29994 eq70801
  have eq70840 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq70821
  have eq70841 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq70840
  have eq70847 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq70841
       grind)
    | exact superpose eq70841 eq8
    | exact resolve eq8 eq70841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70841
  have eq71190 : x = y ∨ x = y := by
    first
    | (have i₁ := eq70847
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq70847
    | exact resolve eq70847 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70847
  have eq71191 : x = y := by grind
  clear eq71190
  have eq71197 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq71191
       grind)
    | exact superpose eq71191 eq14
    | exact resolve eq14 eq71191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71191
  have eq71198 : False := by grind
  exact eq71198

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq36 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq35
    | (have j0 := eq35 X0 X1
       grind)
    | exact resolve eq35 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq86 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq43 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq8
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq8 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq186 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq175
    | (have j0 := eq175 X0 X1
       grind)
    | exact resolve eq175 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1172 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq186 x y
       grind)
    | exact superpose eq186 eq14
    | (have j1 := eq186 x y
       grind)
    | exact resolve eq14 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1346 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq36
    | exact resolve eq36 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1493 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1346 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1346
    | (have j0 := eq1346 X0 X1
       grind)
    | exact resolve eq1346 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1877 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1 (σ X0)
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq86
    | (have j0 := eq86 X1 (σ X0)
       grind)
    | (have r₁ := eq86 X0 (σ X0)
       have r₂ := eq27 X0
       grind)
    | exact resolve eq86 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1906 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1877 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1877
    | (have j0 := eq1877 X0 X1
       grind)
    | exact resolve eq1877 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq23015 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1172
       have i₂ := eq1493 x y
       grind)
    | exact superpose eq1493 eq1172
    | (have j1 := eq1493 x y
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 x y
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1172 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172 eq1493
  have eq23016 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23015
  have eq23017 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23016
  have eq23076 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq23017
       grind)
    | exact superpose eq23017 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq23017
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq23017
       grind)
    | exact resolve eq10 eq23017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23111 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1906 X0 y
       have i₂ := eq23017
       grind)
    | exact superpose eq23017 eq1906
    | (have j0 := eq1906 X0 x
       grind)
    | exact resolve eq1906 eq23017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906 eq23017
  have eq29022 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq23076 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23076
  have eq69287 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq23111 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23111
  have eq69293 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq69287
       grind)
    | exact superpose eq69287 eq14
    | exact resolve eq14 eq69287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69287
  have eq69310 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq69293
       have i₂ := eq29022
       grind)
    | exact superpose eq29022 eq69293
    | exact resolve eq69293 eq29022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29022 eq69293
  have eq69334 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq69310
  have eq69335 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq69334
  have eq69341 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq69335
       grind)
    | exact superpose eq69335 eq8
    | exact resolve eq8 eq69335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69335
  have eq69685 : x = y ∨ x = y := by
    first
    | (have i₁ := eq69341
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq69341
    | exact resolve eq69341 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69341
  have eq69686 : x = y := by grind
  clear eq69685
  have eq69692 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq69686
       grind)
    | exact superpose eq69686 eq14
    | exact resolve eq14 eq69686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69686
  have eq69693 : False := by grind
  exact eq69693

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq33 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ X1 = X2 ∨ (k X0 X2) = (M.op X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq12 X1 X2
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2
       have i₂ := eq12 X0 X2
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X2 X1) ∨ (k X0 X2) = (M.op X2 X0) ∨ X1 = X2 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X1 X1 X2
       have j1 := eq39 X1 X1 X2
       grind)
    | (have r₁ := eq33 X0 X1 X2
       have r₂ := eq39 X0 X1 X2
       grind)
    | (have r₁ := eq33 X1 X0 X2
       have r₂ := eq39 X0 X1 X2
       grind)
    | (have r₁ := eq33 X0 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq39 X0 X1 X2
       grind)
    | exact resolve eq33 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq39
  have eq100 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq101 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq186 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq102 (σ X1) (σ X0)
       grind)
    | exact superpose eq102 eq13
    | (have j1 := eq102 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq13 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq102 (τ X1) X0
       grind)
    | exact superpose eq102 eq16
    | (have j1 := eq102 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq16 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq102
  have eq456 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq188
    | exact resolve eq188 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq481 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq456
    | (have j0 := eq456 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq456 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq1475 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq186 x y
       grind)
    | exact superpose eq186 eq14
    | (have j1 := eq186 x y
       grind)
    | exact resolve eq14 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1567 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1475
       have i₂ := eq481 y x
       grind)
    | exact superpose eq481 eq1475
    | (have j1 := eq481 (σ x) (σ y)
       grind)
    | (have r₁ := eq1475
       have r₂ := eq481 y x
       grind)
    | (have r₁ := eq1475
       have r₂ := eq481 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1475
       have r₂ := eq481 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1475 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481 eq1475
  have eq1568 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1567
  have eq1647 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1568
       grind)
    | exact superpose eq1568 eq8
    | exact resolve eq8 eq1568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568
  have eq1691 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1647
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1647
    | exact resolve eq1647 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq1692 : x = y := by grind
  clear eq1691
  have eq1766 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1692
       grind)
    | exact superpose eq1692 eq14
    | exact resolve eq14 eq1692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq1767 : False := by grind
  exact eq1767

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq36 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq35
    | (have j0 := eq35 X0 X1
       grind)
    | exact resolve eq35 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq86 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq43 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq8
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq8 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq186 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq175
    | (have j0 := eq175 X0 X1
       grind)
    | exact resolve eq175 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1172 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq186 x y
       grind)
    | exact superpose eq186 eq14
    | (have j1 := eq186 x y
       grind)
    | exact resolve eq14 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1346 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq36
    | exact resolve eq36 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1493 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1346 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1346
    | (have j0 := eq1346 X0 X1
       grind)
    | exact resolve eq1346 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1877 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1 (σ X0)
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq86
    | (have j0 := eq86 X1 (σ X0)
       grind)
    | (have r₁ := eq86 X0 (σ X0)
       have r₂ := eq27 X0
       grind)
    | exact resolve eq86 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1906 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1877 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1877
    | (have j0 := eq1877 X0 X1
       grind)
    | exact resolve eq1877 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq22178 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1172
       have i₂ := eq1493 x y
       grind)
    | exact superpose eq1493 eq1172
    | (have j1 := eq1493 x y
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 x y
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1172
       have r₂ := eq1493 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1172 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172 eq1493
  have eq22179 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22178
  have eq22180 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22179
  have eq22239 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq22180
       grind)
    | exact superpose eq22180 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq22180
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq22180
       grind)
    | exact resolve eq10 eq22180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22274 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1906 X0 y
       have i₂ := eq22180
       grind)
    | exact superpose eq22180 eq1906
    | (have j0 := eq1906 X0 x
       grind)
    | exact resolve eq1906 eq22180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906 eq22180
  have eq28185 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq22239 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22239
  have eq67940 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq22274 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22274
  have eq67950 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq67940
       grind)
    | exact superpose eq67940 eq14
    | exact resolve eq14 eq67940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67940
  have eq67970 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq67950
       have i₂ := eq28185
       grind)
    | exact superpose eq28185 eq67950
    | exact resolve eq67950 eq28185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28185 eq67950
  have eq67994 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq67970
  have eq67995 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq67994
  have eq67997 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq67995
       grind)
    | exact superpose eq67995 eq8
    | exact resolve eq8 eq67995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67995
  have eq68337 : x = y ∨ x = y := by
    first
    | (have i₁ := eq67997
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq67997
    | exact resolve eq67997 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67997
  have eq68338 : x = y := by grind
  clear eq68337
  have eq68341 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq68338
       grind)
    | exact superpose eq68338 eq14
    | exact resolve eq14 eq68338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68338
  have eq68342 : False := by grind
  exact eq68342
