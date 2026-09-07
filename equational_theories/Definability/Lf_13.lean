import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyy_pxy_x_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq41 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X2 X1) = X2 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq12 X2 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq12 X2 X1
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X2 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X2 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq53 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X1) = X2 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq41 X2 X1 X2
       have j1 := eq47 X2 X1 X2
       grind)
    | (have r₁ := eq41 X0 X1 X2
       have r₂ := eq47 X0 X1 X2
       grind)
    | (have r₁ := eq41 X2 X1 X0
       have r₂ := eq47 X0 X1 X2
       grind)
    | (have r₁ := eq41 X0 X1 (M.op X2 X1)
       have r₂ := eq47 (M.op X2 X1) X1 X2
       grind)
    | exact resolve eq41 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq47
  have eq70 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq48 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq71 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq70 X0
       have j1 := eq10 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq70 x
       have r₂ := eq10 (M.op x x) x
       grind)
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq79 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq50
    | (have j0 := eq50 (σ X1) (σ X0)
       grind)
    | exact resolve eq50 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq111 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq141 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq142 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq141 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq143 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq267 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq271 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       have j1 := eq111 X0 X1
       grind)
    | (have r₁ := eq267 X0 X1
       have r₂ := eq111 X0 X1
       grind)
    | exact resolve eq267 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq267
  have eq315 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq71 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq71
    | exact resolve eq71 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq315 X0
       have i₂ := eq13 (M.op X0 X0) X0
       grind)
    | exact superpose eq13 eq315
    | exact resolve eq315 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq327 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq323 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq323
    | exact resolve eq323 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq323
  have eq336 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq143 X0 (τ X1)
       grind)
    | exact superpose eq143 eq16
    | (have j1 := eq143 X0 (τ X1)
       grind)
    | exact resolve eq16 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq143
  have eq637 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq271 x y
       grind)
    | exact superpose eq271 eq14
    | (have j1 := eq271 x y
       grind)
    | exact resolve eq14 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq271 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq2357 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq336
    | exact resolve eq336 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq2446 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2357 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2357
    | (have j0 := eq2357 X0 X1
       grind)
    | exact resolve eq2357 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2357
  have eq3294 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq637
       have i₂ := eq2446 y x
       grind)
    | exact superpose eq2446 eq637
    | (have j1 := eq2446 (σ y) (σ x)
       grind)
    | (have r₁ := eq637
       have r₂ := eq2446 y x
       grind)
    | exact resolve eq637 eq2446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq3295 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3294
  have eq3618 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3295
       grind)
    | exact superpose eq3295 eq14
    | exact resolve eq14 eq3295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3619 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq3295
       grind)
    | exact superpose eq3295 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq3295
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq3295
       grind)
    | exact resolve eq11 eq3295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3622 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3619
  have eq3623 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3622
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq3622
    | exact resolve eq3622 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3622
  have eq3627 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3623
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq3623
    | exact resolve eq3623 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3623
  have eq5242 : (σ x) ≠ (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79 y (σ x)
       have i₂ := eq3295
       grind)
    | exact superpose eq3295 eq79
    | exact resolve eq79 eq3295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq3295
  have eq5250 : (σ x) = (σ (k x y)) ∨ (σ x) ≠ (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5242
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq5242
    | exact resolve eq5242 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5242
  have eq5266 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5250
       have r₂ := eq3627
       grind)
    | exact resolve eq5250 eq3627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3627 eq5250
  have eq5842 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2446 y x
       have i₂ := eq5266
       grind)
    | exact superpose eq5266 eq2446
    | (have j0 := eq2446 y x
       grind)
    | exact resolve eq2446 eq5266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2446 eq5266
  have eq5913 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq5842
  have eq5938 : x = (M.op x y) := by
    first
    | (have r₁ := eq5913
       have r₂ := eq3618
       grind)
    | exact resolve eq5913 eq3618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3618 eq5913
  have eq6440 : x ≠ x ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq5938
       grind)
    | exact superpose eq5938 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq5938
       grind)
    | exact resolve eq11 eq5938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6442 : x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq6440
  have eq6597 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq653 x y
       have i₂ := eq6442
       grind)
    | exact superpose eq6442 eq653
    | (have j0 := eq653 x y
       grind)
    | exact resolve eq653 eq6442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq6442
  have eq6604 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq6597
  have eq7014 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq6604
       grind)
    | exact superpose eq6604 eq14
    | exact resolve eq14 eq6604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6604
  have eq7022 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq7014
       have i₂ := eq5938
       grind)
    | exact superpose eq5938 eq7014
    | exact resolve eq7014 eq5938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5938 eq7014
  have eq7023 : x = (M.op y y) := by grind
  clear eq7022
  have eq7288 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq327 y
       have i₂ := eq7023
       grind)
    | exact superpose eq7023 eq327
    | exact resolve eq327 eq7023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq7023
  have eq7302 : False := by grind
  exact eq7302

/-- `x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyy_pxy_y_pxy_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq41 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X2 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq12 X2 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq12 X2 X1
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X2 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X2 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq53 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq41 X2 X1 X2
       have j1 := eq47 X2 X1 X2
       grind)
    | (have r₁ := eq41 X0 X1 X2
       have r₂ := eq47 X0 X1 X2
       grind)
    | (have r₁ := eq41 X2 X1 X0
       have r₂ := eq47 X0 X1 X2
       grind)
    | exact resolve eq41 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq47
  have eq77 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq50
    | (have j0 := eq50 (σ X1) (σ X0)
       grind)
    | exact resolve eq50 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq109 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq139 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq140 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq139 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq141 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq140 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq266 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq272 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq266 X0 X1
       have j1 := eq109 X0 X1
       grind)
    | (have r₁ := eq266 X0 X1
       have r₂ := eq109 X0 X1
       grind)
    | exact resolve eq266 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq266
  have eq319 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq141 (τ X0) X1
       grind)
    | exact superpose eq141 eq15
    | (have j1 := eq141 (τ X0) X1
       grind)
    | exact resolve eq15 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq595 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq272 x y
       grind)
    | exact superpose eq272 eq14
    | (have j1 := eq272 x y
       grind)
    | exact resolve eq14 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq2137 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq319 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq319
    | exact resolve eq319 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq2224 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2137 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2137
    | (have j0 := eq2137 X0 X1
       grind)
    | exact resolve eq2137 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2137
  have eq2872 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq595
       have i₂ := eq2224 x y
       grind)
    | exact superpose eq2224 eq595
    | (have j1 := eq2224 (σ x) (σ y)
       grind)
    | (have r₁ := eq595
       have r₂ := eq2224 x y
       grind)
    | exact resolve eq595 eq2224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2873 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2872
  have eq3058 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2873
       grind)
    | exact superpose eq2873 eq14
    | exact resolve eq14 eq2873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3059 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq2873
       grind)
    | exact superpose eq2873 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq2873
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq2873
       grind)
    | exact resolve eq11 eq2873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3062 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3059
  have eq3063 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3062
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq3062
    | exact resolve eq3062 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3062
  have eq3067 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3063
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq3063
    | exact resolve eq3063 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3063
  have eq3732 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq77 y (σ x)
       have i₂ := eq2873
       grind)
    | exact superpose eq2873 eq77
    | exact resolve eq77 eq2873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2873
  have eq3740 : (σ y) = (σ (k x y)) ∨ (σ y) ≠ (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3732
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq3732
    | exact resolve eq3732 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3732
  have eq3754 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3740
       have r₂ := eq3067
       grind)
    | exact resolve eq3740 eq3067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3067 eq3740
  have eq4048 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2224 x y
       have i₂ := eq3754
       grind)
    | exact superpose eq3754 eq2224
    | (have j0 := eq2224 x y
       grind)
    | exact resolve eq2224 eq3754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224 eq3754
  have eq4098 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq4048
  have eq4123 : y = (M.op x y) := by
    first
    | (have r₁ := eq4098
       have r₂ := eq3058
       grind)
    | exact resolve eq4098 eq3058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3058 eq4098
  have eq4419 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq4123
       grind)
    | exact superpose eq4123 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq4123
       grind)
    | exact resolve eq11 eq4123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4421 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq4419
  have eq4847 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq607 x y
       have i₂ := eq4421
       grind)
    | exact superpose eq4421 eq607
    | (have j0 := eq607 x y
       grind)
    | exact resolve eq607 eq4421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607 eq4421
  have eq4854 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq4847
  have eq5933 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4854
       grind)
    | exact superpose eq4854 eq14
    | exact resolve eq14 eq4854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4854
  have eq5943 : (σ y) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5933
       have i₂ := eq4123
       grind)
    | exact superpose eq4123 eq5933
    | exact resolve eq5933 eq4123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5933
  have eq5944 : y = (M.op y y) := by grind
  clear eq5943
  have eq6080 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq5944
       grind)
    | exact superpose eq5944 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq5944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5944
  have eq6093 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq6080 X0
       have j1 := eq141 X0 y
       grind)
    | (have r₁ := eq6080 X0
       have r₂ := eq141 X0 y
       grind)
    | exact resolve eq6080 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq6080
  have eq6256 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq595
       have i₂ := eq6093 x
       grind)
    | exact superpose eq6093 eq595
    | exact resolve eq595 eq6093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq6093
  have eq6259 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6256
  have eq6520 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq6259
       grind)
    | exact superpose eq6259 eq14
    | exact resolve eq14 eq6259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6259
  have eq6531 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq6520
       have i₂ := eq4123
       grind)
    | exact superpose eq4123 eq6520
    | exact resolve eq6520 eq4123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4123 eq6520
  have eq6532 : False := by grind
  exact eq6532

/-- `x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyy_pyx_pyy_pyx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq64 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq64 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq64 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | exact resolve eq64 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq219 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq72 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq226 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq219 X0 X1
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq219 X1 X1
       have r₂ := eq68 X1 X1
       grind)
    | (have r₁ := eq219 X1 X0
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq219 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq219
  have eq254 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq226 (σ X1) (σ X0)
       grind)
    | exact superpose eq226 eq13
    | exact resolve eq13 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 X1
       have i₂ := eq226 X1 X0
       grind)
    | exact superpose eq226 eq254
    | exact resolve eq254 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq254
  have eq1296 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq261 x y
       grind)
    | exact superpose eq261 eq14
    | (have r₁ := eq14
       have r₂ := eq261 x y
       grind)
    | exact resolve eq14 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq1328 : False := by grind
  exact eq1328

/-- `x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyy_pyx_x_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq51 (σ X0) (σ X1)
       grind)
    | exact superpose eq51 eq13
    | (have j1 := eq51 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq51 (τ X0) X1
       grind)
    | exact superpose eq51 eq16
    | (have j1 := eq51 (τ X0) X1
       grind)
    | exact resolve eq16 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq51
  have eq81 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq74
    | exact resolve eq74 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq437 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq399 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq399
    | (have j0 := eq399 X0 X1
       grind)
    | exact resolve eq399 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq599 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq71 x y
       grind)
    | exact superpose eq71 eq14
    | (have j1 := eq71 x y
       grind)
    | exact resolve eq14 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq2167 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq599
       have i₂ := eq437 x y
       grind)
    | exact superpose eq437 eq599
    | (have j1 := eq437 (σ x) (σ y)
       grind)
    | (have r₁ := eq599
       have r₂ := eq437 x y
       grind)
    | exact resolve eq599 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq2168 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2167
  have eq2172 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2168
       grind)
    | exact superpose eq2168 eq14
    | exact resolve eq14 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2175 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq2168
       grind)
    | exact superpose eq2168 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq2168
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq2168
       grind)
    | exact resolve eq11 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2176 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2175
  have eq2177 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2176
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq2176
    | exact resolve eq2176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2176
  have eq2179 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2177
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq2177
    | exact resolve eq2177 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177
  have eq37274 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq81 x (σ y)
       have i₂ := eq2179
       grind)
    | exact superpose eq2179 eq81
    | (have j0 := eq81 x (σ y)
       grind)
    | (have r₁ := eq81 x (σ y)
       have r₂ := eq2179
       grind)
    | exact resolve eq81 eq2179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq2179
  have eq37279 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq37274
  have eq37284 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37279
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq37279
    | exact resolve eq37279 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37279
  have eq66427 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2168
       have i₂ := eq37284
       grind)
    | exact superpose eq37284 eq2168
    | exact resolve eq2168 eq37284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168 eq37284
  have eq66436 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq66427
  have eq67472 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq437 x y
       have i₂ := eq66436
       grind)
    | exact superpose eq66436 eq437
    | (have j0 := eq437 x y
       grind)
    | exact resolve eq437 eq66436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq66436
  have eq67552 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq67472
  have eq67577 : y = (M.op x y) := by
    first
    | (have r₁ := eq67552
       have r₂ := eq2172
       grind)
    | exact resolve eq67552 eq2172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172 eq67552
  have eq68298 : y ≠ y ∨ (M.op x x) = (M.op y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq67577
       grind)
    | exact superpose eq67577 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq67577
       grind)
    | exact resolve eq11 eq67577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68301 : y = (k y x) ∨ (M.op x x) = (M.op y x) := by grind
  clear eq68298
  have eq69392 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq610 x y
       have i₂ := eq68301
       grind)
    | exact superpose eq68301 eq610
    | (have j0 := eq610 x y
       grind)
    | exact resolve eq610 eq68301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68301
  have eq69461 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) := by grind
  clear eq69392
  have eq71071 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq69461
       grind)
    | exact superpose eq69461 eq14
    | exact resolve eq14 eq69461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69461
  have eq71079 : (σ y) ≠ (σ y) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq71071
       have i₂ := eq67577
       grind)
    | exact superpose eq67577 eq71071
    | exact resolve eq71071 eq67577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71071
  have eq71080 : (M.op x x) = (M.op y x) := by grind
  clear eq71079
  have eq71907 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq71080
       grind)
    | exact superpose eq71080 eq10
    | (have j0 := eq10 x x
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq71080
       grind)
    | exact resolve eq10 eq71080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71080
  have eq71922 : (M.op x y) = (k y x) := by grind
  clear eq71907
  have eq71924 : y = (k y x) := by
    first
    | (have i₁ := eq71922
       have i₂ := eq67577
       grind)
    | exact superpose eq67577 eq71922
    | exact resolve eq71922 eq67577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71922
  have eq72720 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq610 x y
       have i₂ := eq71924
       grind)
    | exact superpose eq71924 eq610
    | (have j0 := eq610 x y
       grind)
    | exact resolve eq610 eq71924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610 eq71924
  have eq72790 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq72720
  have eq74443 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq72790
       grind)
    | exact superpose eq72790 eq14
    | exact resolve eq14 eq72790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72790
  have eq74451 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq74443
       have i₂ := eq67577
       grind)
    | exact superpose eq67577 eq74443
    | exact resolve eq74443 eq67577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67577 eq74443
  have eq74452 : False := by grind
  exact eq74452

/-- `x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyy_pyx_y_pyx_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 (M.op X0 X0) X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq51 (σ X0) (σ X1)
       grind)
    | exact superpose eq51 eq13
    | (have j1 := eq51 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq51 X0 (τ X1)
       grind)
    | exact superpose eq51 eq15
    | (have j1 := eq51 X0 (τ X1)
       grind)
    | exact resolve eq15 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq51
  have eq81 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq72
    | exact resolve eq72 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq437 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq399 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq399
    | (have j0 := eq399 X0 X1
       grind)
    | exact resolve eq399 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq599 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq71 x y
       grind)
    | exact superpose eq71 eq14
    | (have j1 := eq71 x y
       grind)
    | exact resolve eq14 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq2167 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq599
       have i₂ := eq437 y x
       grind)
    | exact superpose eq437 eq599
    | (have j1 := eq437 (σ y) (σ x)
       grind)
    | (have r₁ := eq599
       have r₂ := eq437 y x
       grind)
    | exact resolve eq599 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq2168 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2167
  have eq2172 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2168
       grind)
    | exact superpose eq2168 eq14
    | exact resolve eq14 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2175 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq2168
       grind)
    | exact superpose eq2168 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq2168
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq2168
       grind)
    | exact resolve eq11 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2176 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2175
  have eq2177 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2176
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq2176
    | exact resolve eq2176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2176
  have eq2179 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2177
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq2177
    | exact resolve eq2177 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177
  have eq39863 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq81 x (σ y)
       have i₂ := eq2179
       grind)
    | exact superpose eq2179 eq81
    | (have j0 := eq81 x (σ y)
       grind)
    | (have r₁ := eq81 x (σ y)
       have r₂ := eq2179
       grind)
    | exact resolve eq81 eq2179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq2179
  have eq39868 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq39863
  have eq39873 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39868
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq39868
    | exact resolve eq39868 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39868
  have eq68277 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2168
       have i₂ := eq39873
       grind)
    | exact superpose eq39873 eq2168
    | exact resolve eq2168 eq39873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168 eq39873
  have eq68286 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq68277
  have eq69350 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq437 y x
       have i₂ := eq68286
       grind)
    | exact superpose eq68286 eq437
    | (have j0 := eq437 y x
       grind)
    | exact resolve eq437 eq68286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq68286
  have eq69430 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq69350
  have eq69455 : x = (M.op x y) := by
    first
    | (have r₁ := eq69430
       have r₂ := eq2172
       grind)
    | exact resolve eq69430 eq2172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2172 eq69430
  have eq70790 : x ≠ x ∨ (M.op x x) = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq69455
       grind)
    | exact superpose eq69455 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq69455
       grind)
    | exact resolve eq11 eq69455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70793 : x = (k y x) ∨ (M.op x x) = (M.op y x) := by grind
  clear eq70790
  have eq71513 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq610 x y
       have i₂ := eq70793
       grind)
    | exact superpose eq70793 eq610
    | (have j0 := eq610 x y
       grind)
    | exact resolve eq610 eq70793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70793
  have eq71582 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) := by grind
  clear eq71513
  have eq73734 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq71582
       grind)
    | exact superpose eq71582 eq14
    | exact resolve eq14 eq71582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71582
  have eq73742 : (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq73734
       have i₂ := eq69455
       grind)
    | exact superpose eq69455 eq73734
    | exact resolve eq73734 eq69455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73734
  have eq73743 : (M.op x x) = (M.op y x) := by grind
  clear eq73742
  have eq74068 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq73743
       grind)
    | exact superpose eq73743 eq10
    | (have j0 := eq10 x x
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq73743
       grind)
    | exact resolve eq10 eq73743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73743
  have eq74083 : (M.op x y) = (k y x) := by grind
  clear eq74068
  have eq74085 : x = (k y x) := by
    first
    | (have i₁ := eq74083
       have i₂ := eq69455
       grind)
    | exact superpose eq69455 eq74083
    | exact resolve eq74083 eq69455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74083
  have eq75153 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq610 x y
       have i₂ := eq74085
       grind)
    | exact superpose eq74085 eq610
    | (have j0 := eq610 x y
       grind)
    | exact resolve eq610 eq74085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610 eq74085
  have eq75223 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq75153
  have eq76642 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq75223
       grind)
    | exact superpose eq75223 eq14
    | exact resolve eq14 eq75223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75223
  have eq76650 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq76642
       have i₂ := eq69455
       grind)
    | exact superpose eq69455 eq76642
    | exact resolve eq76642 eq69455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69455 eq76642
  have eq76651 : False := by grind
  exact eq76651

/-- `x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyy_x_y_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq31 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ X1 = X2 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq12 X2 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq12 X2 X1
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X2 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X2 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | exact resolve eq32 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq41 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X1 = X2 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq31 X2 X1 X2
       have j1 := eq36 X2 X1 X2
       grind)
    | (have r₁ := eq31 X0 X1 X2
       have r₂ := eq36 X0 X1 X2
       grind)
    | (have r₁ := eq31 X2 X1 X0
       have r₂ := eq36 X0 X1 X2
       grind)
    | (have r₁ := eq31 X0 (M.op X0 X1) (M.op X2 X1)
       have r₂ := eq36 X0 X1 X2
       grind)
    | exact resolve eq31 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq36
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq38
    | (have j0 := eq38 (σ (k X0 X1)) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq38 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq113 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq114 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq113 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq196 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq77 (k X0 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq77 (M.op X1 X1) (k X0 X1)
       grind)
    | exact resolve eq196 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq196
  have eq260 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq115 (τ X0) X1
       grind)
    | exact superpose eq115 eq16
    | (have j1 := eq115 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq16 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq115
  have eq564 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq260 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq260
    | exact resolve eq260 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq597 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq564 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq564
    | (have j0 := eq564 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq564 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq612 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq204 x y
       grind)
    | exact superpose eq204 eq14
    | (have j1 := eq204 x y
       grind)
    | exact resolve eq14 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq915 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq612
       have i₂ := eq597 x y
       grind)
    | exact superpose eq597 eq612
    | (have j1 := eq597 (σ x) (σ y)
       grind)
    | (have r₁ := eq612
       have r₂ := eq597 x y
       grind)
    | (have r₁ := eq612
       have r₂ := eq597 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq612
       have r₂ := eq597 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq612 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq612
  have eq916 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq915
  have eq1027 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq916
       grind)
    | exact superpose eq916 eq8
    | exact resolve eq8 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq1063 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1027
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1027
    | exact resolve eq1027 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1064 : x = y := by grind
  clear eq1063
  have eq1164 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1064
       grind)
    | exact superpose eq1064 eq14
    | exact resolve eq14 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1165 : False := by grind
  exact eq1165

/-- `x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyy_x_y_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq31 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ X1 = X2 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq12 X2 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq12 X2 X1
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X2 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X2 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | exact resolve eq32 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq41 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X1 = X2 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq31 X2 X1 X2
       have j1 := eq36 X2 X1 X2
       grind)
    | (have r₁ := eq31 X0 X1 X2
       have r₂ := eq36 X0 X1 X2
       grind)
    | (have r₁ := eq31 X2 X1 X0
       have r₂ := eq36 X0 X1 X2
       grind)
    | (have r₁ := eq31 X0 (M.op X0 X1) (M.op X2 X1)
       have r₂ := eq36 X0 X1 X2
       grind)
    | exact resolve eq31 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq36
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq38
    | (have j0 := eq38 (σ (k X0 X1)) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq38 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq113 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq114 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq113 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq196 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq77 (k X0 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq77 (M.op X1 X1) (k X0 X1)
       grind)
    | exact resolve eq196 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq196
  have eq260 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq115 (τ X0) X1
       grind)
    | exact superpose eq115 eq16
    | (have j1 := eq115 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq16 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq115
  have eq564 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq260 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq260
    | exact resolve eq260 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq597 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq564 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq564
    | (have j0 := eq564 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq564 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq612 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq204 x y
       grind)
    | exact superpose eq204 eq14
    | (have j1 := eq204 x y
       grind)
    | exact resolve eq14 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq915 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq612
       have i₂ := eq597 x y
       grind)
    | exact superpose eq597 eq612
    | (have j1 := eq597 (σ x) (σ y)
       grind)
    | (have r₁ := eq612
       have r₂ := eq597 x y
       grind)
    | (have r₁ := eq612
       have r₂ := eq597 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq612
       have r₂ := eq597 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq612 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq612
  have eq916 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq915
  have eq1027 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq916
       grind)
    | exact superpose eq916 eq8
    | exact resolve eq8 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq1063 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1027
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1027
    | exact resolve eq1027 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1064 : x = y := by grind
  clear eq1063
  have eq1164 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1064
       grind)
    | exact superpose eq1064 eq14
    | exact resolve eq14 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1165 : False := by grind
  exact eq1165

/-- `x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyy_x_y_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq57 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq39 (σ X0) (σ X1)
       grind)
    | exact superpose eq39 eq13
    | (have j1 := eq39 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq13 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq39 X0 (τ X1)
       grind)
    | exact superpose eq39 eq16
    | (have j1 := eq39 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq39
  have eq205 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq58
    | exact resolve eq58 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq227 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq205
    | (have j0 := eq205 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq205 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq584 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq57 x y
       grind)
    | exact superpose eq57 eq14
    | (have j1 := eq57 x y
       grind)
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq686 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq584
       have i₂ := eq227 y x
       grind)
    | exact superpose eq227 eq584
    | (have j1 := eq227 (σ x) (σ y)
       grind)
    | (have r₁ := eq584
       have r₂ := eq227 y x
       grind)
    | (have r₁ := eq584
       have r₂ := eq227 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq584
       have r₂ := eq227 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq584 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq584
  have eq687 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq686
  have eq780 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq687
       grind)
    | exact superpose eq687 eq8
    | exact resolve eq8 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq815 : x = y ∨ x = y := by
    first
    | (have i₁ := eq780
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq780
    | exact resolve eq780 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq816 : x = y := by grind
  clear eq815
  have eq995 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq816
       grind)
    | exact superpose eq816 eq14
    | exact resolve eq14 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq996 : False := by grind
  exact eq996
