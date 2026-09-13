import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else if m(X,X) = m(X,Y) then m(X,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxy_y_pxy_x_pxx_pxy_x_y_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq68 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq68
    | exact resolve eq68 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq72
    | exact resolve eq72 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq78 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq76
    | exact resolve eq76 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78
    | exact resolve eq78 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq97 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq99 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq179 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq461 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq100 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq100
    | (have j0 := eq100 (σ X0)
       grind)
    | exact resolve eq100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq100 x
       grind)
    | exact superpose eq100 eq43
    | (have j1 := eq100 x
       grind)
    | exact resolve eq43 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq702 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq64 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq64 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq64 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq64 X1 X1
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq715 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq702 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq719 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq715 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq715
    | (have j0 := eq715 X0 X1
       grind)
    | exact resolve eq715 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq2975 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq461 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq4427 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq179 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq179
    | (have j0 := eq179 x
       grind)
    | exact resolve eq179 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq4445 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4427
    | exact resolve eq4427 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4427
  have eq4461 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4445
    | exact resolve eq4445 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4445
  have eq4466 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4461
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq4461
    | exact resolve eq4461 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4461
  have eq4467 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4466
    | exact resolve eq4466 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4466
  have eq4468 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq4467
    | exact resolve eq4467 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4467
  have eq7384 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq719 X0 X1
       have j1 := eq711 X0 X1
       grind)
    | (have r₁ := eq719 X0 X1
       have r₂ := eq711 X0 (k X0 X1)
       grind)
    | (have r₁ := eq719 X0 X1
       have r₂ := eq711 X0 X0
       grind)
    | (have r₁ := eq719 X0 X1
       have r₂ := eq711 X0 X1
       grind)
    | exact resolve eq719 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq719
  have eq7385 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7384 X0 X1
       have j1 := eq710 X0 X1
       grind)
    | (have r₁ := eq7384 X0 X1
       have r₂ := eq710 X0 X1
       grind)
    | (have r₁ := eq7384 X0 X0
       have r₂ := eq710 X0 X0
       grind)
    | exact resolve eq7384 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq7384
  have eq7386 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7385 X0 X1
       have j1 := eq709 X0 X1
       grind)
    | (have r₁ := eq7385 X0 X1
       have r₂ := eq709 X0 X1
       grind)
    | (have r₁ := eq7385 X0 X0
       have r₂ := eq709 X0 X1
       grind)
    | exact resolve eq7385 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq7385
  have eq7580 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq7386 X0 X1
       grind)
    | exact superpose eq7386 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       have j1 := eq7386 X0 X1
       grind)
    | (have r₁ := eq14 (σ X0) (σ X0)
       have r₂ := eq7386 X0 X0
       grind)
    | (have r₁ := eq14 (σ X0) (σ X1)
       have r₂ := eq7386 X0 X1
       grind)
    | exact resolve eq14 eq7386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7386
  have eq7598 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7580 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq7580 X0 X0
       have r₂ := eq14 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq7580 X0 X1
       have r₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq7580 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7580
  have eq7609 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7598 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq7598
    | (have j0 := eq7598 X0 X1
       grind)
    | exact resolve eq7598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7598
  have eq15796 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq79 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15796
    | exact resolve eq15796 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15796
  have eq15808 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15797
       have r₂ := eq27
       grind)
    | exact resolve eq15797 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15797
  have eq15810 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15808
    | exact resolve eq15808 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15808
  have eq15812 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15810
    | exact resolve eq15810 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15810
  have eq15814 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15812
    | exact resolve eq15812 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15812
  have eq15817 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15814 eq98
    | (have r₁ := eq98
       have r₂ := eq15814
       grind)
    | exact resolve eq98 eq15814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15814
  have eq15825 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15817
  have eq15826 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15825
  have eq15859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15826 eq79
    | exact resolve eq79 eq15826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq15826
  have eq15867 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15859
  have eq15869 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15867
       have r₂ := eq27
       grind)
    | exact resolve eq15867 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15867
  have eq15871 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq466
       have i₂ := eq15869
       grind)
    | exact superpose eq15869 eq466
    | exact resolve eq466 eq15869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq15872 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97
       have i₂ := eq15869
       grind)
    | exact superpose eq15869 eq97
    | (have r₁ := eq97
       have r₂ := eq15869
       grind)
    | exact resolve eq97 eq15869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15869
  have eq15880 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15872
  have eq15881 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15880
  have eq15882 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15871
  have eq15883 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15882
    | exact resolve eq15882 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15882
  have eq16078 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq15881
       grind)
    | exact superpose eq15881 eq44
    | exact resolve eq44 eq15881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15881
  have eq16096 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq16078
    | exact resolve eq16078 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16078
  have eq16135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16096 eq4468
    | exact resolve eq4468 eq16096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16096
  have eq16139 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq16135
  have eq16143 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16139
       have r₂ := eq27
       grind)
    | exact resolve eq16139 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16139
  have eq16169 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16143 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq16143
       grind)
    | exact resolve eq12 eq16143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16143
  have eq16174 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq16169
  have eq16175 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq16174
  have eq16690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16175 eq15883
    | exact resolve eq15883 eq16175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15883 eq16175
  have eq16694 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16690
  have eq16696 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16694
       have r₂ := eq27
       grind)
    | exact resolve eq16694 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16694
  have eq16698 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16696 eq51
    | (have r₁ := eq51
       have r₂ := eq16696
       grind)
    | exact resolve eq51 eq16696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16696
  have eq16701 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16698
  have eq16959 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16701 eq55
    | exact resolve eq55 eq16701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16701
  have eq16989 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq16959
    | exact resolve eq16959 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16959
  have eq16995 : x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16989
       have r₂ := eq50
       grind)
    | exact resolve eq16989 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16989
  have eq17243 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq16995
       grind)
    | exact superpose eq16995 eq44
    | exact resolve eq44 eq16995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17253 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq16995
       grind)
    | exact superpose eq16995 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq16995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17254 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17253
  have eq17258 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17254
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17254
    | exact resolve eq17254 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17254
  have eq17259 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17258
  have eq17268 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17243
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17243
    | exact resolve eq17243 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17243
  have eq17271 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17259
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17259
    | exact resolve eq17259 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17259
  have eq17273 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17271
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17271
    | exact resolve eq17271 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17271
  have eq17290 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17268 eq4468
    | exact resolve eq4468 eq17268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4468
  have eq17297 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17290
  have eq17322 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97
       have i₂ := eq17273
       grind)
    | exact superpose eq17273 eq97
    | (have r₁ := eq97
       have r₂ := eq17273
       grind)
    | exact resolve eq97 eq17273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17273
  have eq17330 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17322
  have eq17331 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17330
  have eq17577 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17297 eq98
    | (have r₁ := eq98
       have r₂ := eq17297
       grind)
    | exact resolve eq98 eq17297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq17297
  have eq17585 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17577
  have eq17586 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17585
  have eq18117 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16995
       have i₂ := eq17331
       grind)
    | exact superpose eq17331 eq16995
    | exact resolve eq16995 eq17331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16995 eq17331
  have eq18119 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18117
  have eq18131 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18119 eq57
    | (have r₁ := eq57
       have r₂ := eq18119
       grind)
    | exact resolve eq57 eq18119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq18132 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18119 eq51
    | exact resolve eq51 eq18119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq18119
  have eq18134 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18131
  have eq18670 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17586 eq17268
    | exact resolve eq17268 eq17586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17268 eq17586
  have eq18672 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18670
  have eq18682 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18672 eq27
    | exact resolve eq27 eq18672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18672
  have eq19180 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18134 eq55
    | exact resolve eq55 eq18134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq18134
  have eq19219 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq19180
    | exact resolve eq19180 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19180
  have eq19224 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19219
       have r₂ := eq56
       grind)
    | exact resolve eq19219 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19219
  have eq19486 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq19224
       grind)
    | exact superpose eq19224 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq19224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19487 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq19486
  have eq19493 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19487
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19487
    | exact resolve eq19487 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19487
  have eq19494 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq19493
  have eq19507 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19494
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19494
    | exact resolve eq19494 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19494
  have eq19509 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19507
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19507
    | exact resolve eq19507 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19507
  have eq19569 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq19509
       grind)
    | exact superpose eq19509 eq97
    | (have r₁ := eq97
       have r₂ := eq19509
       grind)
    | exact resolve eq97 eq19509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq19509
  have eq19577 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq19569
  have eq19578 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq19577
  have eq19869 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19224
       have i₂ := eq19578
       grind)
    | exact superpose eq19578 eq19224
    | exact resolve eq19224 eq19578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19224 eq19578
  have eq19871 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19869
  have eq20136 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19871 eq29
    | exact resolve eq29 eq19871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20207 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19871 eq18132
    | (have r₁ := eq18132
       have r₂ := eq19871
       grind)
    | exact resolve eq18132 eq19871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18132 eq19871
  have eq20213 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20207
  have eq20214 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20213
  have eq20284 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq20136
    | exact resolve eq20136 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20136
  have eq20285 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20284 eq20
    | exact resolve eq20 eq20284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20287 : y ≠ y ∨ x = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20284 eq50
    | (have r₁ := eq50
       have r₂ := eq20284
       grind)
    | exact resolve eq50 eq20284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20284
  have eq20355 : x = (k x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq20287
  have eq20422 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20285
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20285
    | exact resolve eq20285 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20285
  have eq20676 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20422 eq26
    | exact resolve eq26 eq20422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20750 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20422 eq18682
    | (have r₁ := eq18682
       have r₂ := eq20422
       grind)
    | exact resolve eq18682 eq20422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18682
  have eq20756 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq20750
  have eq20757 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq20756
  have eq20834 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20757 eq27
    | exact resolve eq27 eq20757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21101 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20214 eq49
    | exact resolve eq49 eq20214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq20214
  have eq21133 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq21101
    | exact resolve eq21101 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21101
  have eq21142 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq20355
       grind)
    | exact superpose eq20355 eq44
    | exact resolve eq44 eq20355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq20355
  have eq21176 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21142
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21142
    | exact resolve eq21142 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21142
  have eq21709 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq100 x
       have i₂ := eq21133
       grind)
    | exact superpose eq21133 eq100
    | (have j0 := eq100 x
       grind)
    | exact resolve eq100 eq21133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq21133
  have eq21710 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq21709
  have eq21730 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20676 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20676
       grind)
    | exact resolve eq13 eq20676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20676
  have eq21732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21730
       have r₂ := eq20757
       grind)
    | exact resolve eq21730 eq20757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20757 eq21730
  have eq21733 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21732
       have r₂ := eq27
       grind)
    | exact resolve eq21732 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21732
  have eq21734 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20422 eq21176
    | exact resolve eq21176 eq20422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20422 eq21176
  have eq21778 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq21734
  have eq22343 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21778 eq21733
    | exact resolve eq21733 eq21778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21733 eq21778
  have eq22346 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq22343
  have eq22349 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq22346
       have r₂ := eq20834
       grind)
    | exact resolve eq22346 eq20834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20834 eq22346
  have eq22361 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq22349 eq20
    | exact resolve eq20 eq22349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22364 : x ≠ x ∨ x = y ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq22349 eq56
    | (have r₁ := eq56
       have r₂ := eq22349
       grind)
    | exact resolve eq56 eq22349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq22349
  have eq22435 : x ≠ x ∨ x = y ∨ y = (k x y) := by grind
  clear eq22364
  have eq22436 : y = (k x y) ∨ x = y := by grind
  clear eq22435
  have eq22508 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22361
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22361
    | exact resolve eq22361 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22361
  have eq104724 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq7609 x y
       have i₂ := eq22436
       grind)
    | exact superpose eq22436 eq7609
    | (have j0 := eq7609 x y
       grind)
    | exact resolve eq7609 eq22436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7609 eq22436
  have eq105062 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq104724
  have eq105315 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq105062
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq105062
    | exact resolve eq105062 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105062
  have eq105710 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq105315
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq105315
    | exact resolve eq105315 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105315
  have eq106074 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq105710
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq105710
    | exact resolve eq105710 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105710
  have eq106415 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq106074
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq106074
    | exact resolve eq106074 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106074
  have eq106568 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq106415
    | exact resolve eq106415 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106415
  have eq106847 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq106568 eq27
    | exact resolve eq27 eq106568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106568
  have eq106856 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq106847
       have r₂ := eq22508
       grind)
    | exact resolve eq106847 eq22508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22508 eq106847
  have eq109145 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq106856 eq29
    | exact resolve eq29 eq106856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq106856
  have eq109436 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq109145
    | exact resolve eq109145 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq109145
  have eq109437 : x = y := by grind
  clear eq109436
  have eq109438 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq109437
       grind)
    | exact superpose eq109437 eq18
    | exact resolve eq18 eq109437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq109439 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq109437
       grind)
    | exact superpose eq109437 eq24
    | exact resolve eq24 eq109437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq109707 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq109439
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq109439
    | exact resolve eq109439 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109439
  have eq109709 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq109707 eq26
    | exact resolve eq26 eq109707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq109707
  have eq111070 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21710
       have i₂ := eq109438
       grind)
    | exact superpose eq109438 eq21710
    | exact resolve eq21710 eq109438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21710 eq109438
  have eq111077 : x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq111070
  have eq111080 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq111077
       have i₂ := eq109437
       grind)
    | exact superpose eq109437 eq111077
    | exact resolve eq111077 eq109437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111077
  have eq111081 : x = (M.op x y) := by grind
  clear eq111080
  have eq111089 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq111081 eq20
    | exact resolve eq20 eq111081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq111091 : x ≠ y ∨ x = (k x y) := by
    first
    | exact superpose eq111081 eq50
    | exact resolve eq50 eq111081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq111081
  have eq111390 : x = (k x y) := by
    first
    | (have r₁ := eq111091
       have r₂ := eq109437
       grind)
    | exact resolve eq111091 eq109437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111091
  have eq111392 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq111089
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq111089
    | exact resolve eq111089 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111089
  have eq111448 : x = (k x x) := by
    first
    | (have i₁ := eq111390
       have i₂ := eq109437
       grind)
    | exact superpose eq109437 eq111390
    | exact resolve eq111390 eq109437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109437 eq111390
  have eq113123 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq111392 eq109709
    | exact resolve eq109709 eq111392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109709
  have eq113161 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2975 x
       have i₂ := eq111448
       grind)
    | exact superpose eq111448 eq2975
    | (have j0 := eq2975 x
       grind)
    | exact resolve eq2975 eq111448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2975 eq111448
  have eq113165 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq113161
  have eq113176 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq113165
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq113165
    | exact resolve eq113165 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq113165
  have eq113192 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq111392 eq113176
    | exact resolve eq113176 eq111392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111392 eq113176
  have eq113207 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq113123 eq113192
    | exact resolve eq113192 eq113123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113123 eq113192
  have eq113220 : False := by grind
  exact eq113220

/-- `x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else if m(X,Y) = m(Y,X) then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxy_y_pxy_x_pxy_pyx_x_y_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq65 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq68 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq68
    | exact resolve eq68 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq72
    | exact resolve eq72 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq78 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq76
    | exact resolve eq76 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78
    | exact resolve eq78 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq86 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq98 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq98 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq461 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq99 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq99
    | (have j0 := eq99 (σ X0)
       grind)
    | exact resolve eq99 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq64 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq64 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq64 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq64 X0 X1
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq630 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq620 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq631 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq630 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq635 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq631 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq631
    | (have j0 := eq631 X0 X1
       grind)
    | exact resolve eq631 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq636 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq635 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq2961 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq461 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq3220 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq636 X0 X1
       grind)
    | exact superpose eq636 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       have j1 := eq636 X0 X1
       grind)
    | (have r₁ := eq14 (σ X0) (σ X0)
       have r₂ := eq636 X0 X0
       grind)
    | (have r₁ := eq14 (σ X0) (σ X1)
       have r₂ := eq636 X0 X1
       grind)
    | exact resolve eq14 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq3224 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3220 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq3220 X0 X0
       have r₂ := eq14 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq3220 X0 X1
       have r₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq3220 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3220
  have eq3236 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3224 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq3224
    | (have j0 := eq3224 X0 X1
       grind)
    | exact resolve eq3224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3224
  have eq3327 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq65
    | (have j0 := eq65 y
       grind)
    | exact resolve eq65 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq3342 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3327
    | exact resolve eq3327 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3327
  have eq3358 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3342
    | exact resolve eq3342 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342
  have eq3362 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3358
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3358
    | exact resolve eq3358 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358
  have eq3363 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3362
    | exact resolve eq3362 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3362
  have eq3364 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq3363
    | exact resolve eq3363 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3363
  have eq14720 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq79 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14721 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq14720
    | exact resolve eq14720 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14720
  have eq14732 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14721
       have r₂ := eq27
       grind)
    | exact resolve eq14721 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14721
  have eq14734 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq14732
    | exact resolve eq14732 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14732
  have eq14736 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq14734
    | exact resolve eq14734 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14734
  have eq14738 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq14736
    | exact resolve eq14736 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14736
  have eq14740 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14738 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14738
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14738
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14738
       grind)
    | exact resolve eq12 eq14738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14738
  have eq14747 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14740
       have r₂ := eq26
       grind)
    | exact resolve eq14740 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14740
  have eq14749 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq14747
    | exact resolve eq14747 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14747
  have eq14750 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq14749
  have eq14751 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq14750
    | exact resolve eq14750 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14750
  have eq14752 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq14751
  have eq14782 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14752 eq79
    | exact resolve eq79 eq14752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq14752
  have eq14790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14782
  have eq14792 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14790
       have r₂ := eq27
       grind)
    | exact resolve eq14790 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14790
  have eq14794 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq14792
       grind)
    | exact superpose eq14792 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14792
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14792
       grind)
    | exact resolve eq12 eq14792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14795 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq14792
       grind)
    | exact superpose eq14792 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14792
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14792
       grind)
    | exact resolve eq12 eq14792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14792
  have eq14799 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14795
  have eq14800 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14799
       have r₂ := eq18
       grind)
    | exact resolve eq14799 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14799
  have eq14801 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14794
       have r₂ := eq18
       grind)
    | exact resolve eq14794 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14794
  have eq14802 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14800
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14800
    | exact resolve eq14800 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14800
  have eq14803 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14801
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14801
    | exact resolve eq14801 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14801
  have eq14804 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14803
  have eq14805 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14804
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14804
    | exact resolve eq14804 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14804
  have eq14806 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14805
  have eq14808 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq86
       have i₂ := eq14802
       grind)
    | exact superpose eq14802 eq86
    | exact resolve eq86 eq14802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq14802
  have eq14826 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq14808
    | exact resolve eq14808 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14808
  have eq14828 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq14806
       grind)
    | exact superpose eq14806 eq44
    | exact resolve eq44 eq14806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14806
  have eq14846 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq14828
    | exact resolve eq14828 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14828
  have eq15041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14846 eq3364
    | exact resolve eq3364 eq14846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14846
  have eq15045 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15041
  have eq15049 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15045
       have r₂ := eq27
       grind)
    | exact resolve eq15045 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15045
  have eq15074 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15049 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15049
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15049
       grind)
    | exact resolve eq12 eq15049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15049
  have eq15078 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15074
  have eq15079 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15078
       have r₂ := eq26
       grind)
    | exact resolve eq15078 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15078
  have eq15081 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15079
    | exact resolve eq15079 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15079
  have eq15097 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15081 eq14826
    | exact resolve eq14826 eq15081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14826 eq15081
  have eq15099 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15097
  have eq15101 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15099
       have r₂ := eq27
       grind)
    | exact resolve eq15099 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15099
  have eq15340 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15101 eq51
    | (have r₁ := eq51
       have r₂ := eq15101
       grind)
    | exact resolve eq51 eq15101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15101
  have eq15343 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15340
  have eq15588 : (τ (σ x)) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15343 eq55
    | exact resolve eq55 eq15343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15343
  have eq15618 : x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq15588
    | exact resolve eq15588 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15588
  have eq15624 : x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15618
       have r₂ := eq50
       grind)
    | exact resolve eq15618 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15618
  have eq15630 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq15624
       grind)
    | exact superpose eq15624 eq44
    | exact resolve eq44 eq15624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15640 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq15624
       grind)
    | exact superpose eq15624 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq15624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15641 : x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15640
  have eq15645 : x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15641
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15641
    | exact resolve eq15641 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15641
  have eq15646 : x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15645
  have eq15655 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15630
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15630
    | exact resolve eq15630 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15630
  have eq15658 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15646
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15646
    | exact resolve eq15646 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15646
  have eq15660 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15658
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15658
    | exact resolve eq15658 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15658
  have eq15914 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15655 eq3364
    | exact resolve eq3364 eq15655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364
  have eq15921 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15914
  have eq15945 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq15660
       grind)
    | exact superpose eq15660 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15660
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15660
       grind)
    | exact resolve eq12 eq15660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15660
  have eq15952 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15945
       have r₂ := eq18
       grind)
    | exact resolve eq15945 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15945
  have eq15954 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15952
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15952
    | exact resolve eq15952 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15952
  have eq15955 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15954
  have eq15956 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15955
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15955
    | exact resolve eq15955 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15955
  have eq15957 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15956
  have eq16195 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15921 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15921
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15921
       grind)
    | exact resolve eq12 eq15921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15921
  have eq16202 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16195
       have r₂ := eq26
       grind)
    | exact resolve eq16195 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16195
  have eq16204 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16202
    | exact resolve eq16202 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16202
  have eq16205 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16204
  have eq16206 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16205
    | exact resolve eq16205 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16205
  have eq16207 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16206
  have eq16476 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15624
       have i₂ := eq15957
       grind)
    | exact superpose eq15957 eq15624
    | exact resolve eq15624 eq15957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15624 eq15957
  have eq16478 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16476
  have eq16727 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16478 eq57
    | (have r₁ := eq57
       have r₂ := eq16478
       grind)
    | exact resolve eq57 eq16478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq16728 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16478 eq51
    | exact resolve eq51 eq16478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq16478
  have eq16730 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16727
  have eq17001 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16207 eq15655
    | exact resolve eq15655 eq16207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15655 eq16207
  have eq17003 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17001
  have eq17013 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17003 eq27
    | exact resolve eq27 eq17003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17003
  have eq17738 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16730 eq55
    | exact resolve eq55 eq16730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq16730
  have eq17778 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq17738
    | exact resolve eq17738 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17738
  have eq17783 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17778
       have r₂ := eq56
       grind)
    | exact resolve eq17778 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17778
  have eq17803 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq17783
       grind)
    | exact superpose eq17783 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq17783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17804 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq17803
  have eq17810 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17804
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17804
    | exact resolve eq17804 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17804
  have eq17811 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq17810
  have eq17824 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17811
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17811
    | exact resolve eq17811 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17811
  have eq17826 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17824
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17824
    | exact resolve eq17824 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17824
  have eq18123 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq17826
       grind)
    | exact superpose eq17826 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq17826
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq17826
       grind)
    | exact resolve eq12 eq17826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17826
  have eq18130 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq18123
       have r₂ := eq18
       grind)
    | exact resolve eq18123 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18123
  have eq18132 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18130
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18130
    | exact resolve eq18130 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18130
  have eq18133 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq18132
  have eq18134 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18133
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18133
    | exact resolve eq18133 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18133
  have eq18135 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq18134
  have eq18406 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17783
       have i₂ := eq18135
       grind)
    | exact superpose eq18135 eq17783
    | exact resolve eq17783 eq18135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17783 eq18135
  have eq18408 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18406
  have eq18423 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18408 eq29
    | exact resolve eq29 eq18408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18502 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18408 eq16728
    | (have r₁ := eq16728
       have r₂ := eq18408
       grind)
    | exact resolve eq16728 eq18408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16728 eq18408
  have eq18508 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18502
  have eq18509 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18508
  have eq18586 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq18423
    | exact resolve eq18423 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18423
  have eq18824 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18586 eq20
    | exact resolve eq20 eq18586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18826 : y ≠ y ∨ x = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18586 eq50
    | (have r₁ := eq50
       have r₂ := eq18586
       grind)
    | exact resolve eq50 eq18586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18586
  have eq18893 : x = (k x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq18826
  have eq18959 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18824
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18824
    | exact resolve eq18824 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18824
  have eq18961 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18959 eq26
    | exact resolve eq26 eq18959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19043 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18959 eq17013
    | (have r₁ := eq17013
       have r₂ := eq18959
       grind)
    | exact resolve eq17013 eq18959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17013
  have eq19049 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq19043
  have eq19050 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq19049
  have eq19136 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19050 eq27
    | exact resolve eq27 eq19050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19394 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18509 eq49
    | exact resolve eq49 eq18509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq18509
  have eq19413 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq19394
    | exact resolve eq19394 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19394
  have eq19660 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq18893
       grind)
    | exact superpose eq18893 eq44
    | exact resolve eq44 eq18893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq18893
  have eq19694 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19660
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19660
    | exact resolve eq19660 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19660
  have eq19958 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq99 x
       have i₂ := eq19413
       grind)
    | exact superpose eq19413 eq99
    | (have j0 := eq99 x
       grind)
    | exact resolve eq99 eq19413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq19413
  have eq19959 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq19958
  have eq19975 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18961 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18961
       grind)
    | exact resolve eq13 eq18961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18961
  have eq19977 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19975
       have r₂ := eq19050
       grind)
    | exact resolve eq19975 eq19050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19050 eq19975
  have eq19978 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19977
       have r₂ := eq27
       grind)
    | exact resolve eq19977 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19977
  have eq20218 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18959 eq19694
    | exact resolve eq19694 eq18959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18959 eq19694
  have eq20262 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq20218
  have eq20552 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20262 eq19978
    | exact resolve eq19978 eq20262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19978 eq20262
  have eq20555 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq20552
  have eq20558 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq20555
       have r₂ := eq19136
       grind)
    | exact resolve eq20555 eq19136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19136 eq20555
  have eq20570 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20558 eq20
    | exact resolve eq20 eq20558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20573 : x ≠ x ∨ x = y ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq20558 eq56
    | (have r₁ := eq56
       have r₂ := eq20558
       grind)
    | exact resolve eq56 eq20558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq20558
  have eq20644 : x ≠ x ∨ x = y ∨ y = (k x y) := by grind
  clear eq20573
  have eq20645 : y = (k x y) ∨ x = y := by grind
  clear eq20644
  have eq20717 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq20570
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20570
    | exact resolve eq20570 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20570
  have eq101540 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq3236 x y
       have i₂ := eq20645
       grind)
    | exact superpose eq20645 eq3236
    | (have j0 := eq3236 x y
       grind)
    | exact resolve eq3236 eq20645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3236 eq20645
  have eq101874 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq101540
  have eq102128 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq101874
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq101874
    | exact resolve eq101874 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101874
  have eq102523 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq102128
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102128
    | exact resolve eq102128 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102128
  have eq102886 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq102523
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq102523
    | exact resolve eq102523 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102523
  have eq103226 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq102886
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102886
    | exact resolve eq102886 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102886
  have eq103378 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq103226
    | exact resolve eq103226 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103226
  have eq103652 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq103378 eq27
    | exact resolve eq27 eq103378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103378
  have eq103661 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq103652
       have r₂ := eq20717
       grind)
    | exact resolve eq103652 eq20717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20717 eq103652
  have eq105935 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq103661 eq29
    | exact resolve eq29 eq103661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq103661
  have eq106249 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq105935
    | exact resolve eq105935 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq105935
  have eq106250 : x = y := by grind
  clear eq106249
  have eq106251 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq106250
       grind)
    | exact superpose eq106250 eq18
    | exact resolve eq18 eq106250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq106252 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq106250
       grind)
    | exact superpose eq106250 eq24
    | exact resolve eq24 eq106250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq106532 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq106252
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq106252
    | exact resolve eq106252 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106252
  have eq106534 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq106532 eq26
    | exact resolve eq26 eq106532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq106532
  have eq106789 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19959
       have i₂ := eq106251
       grind)
    | exact superpose eq106251 eq19959
    | exact resolve eq19959 eq106251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19959 eq106251
  have eq106799 : x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq106789
  have eq106802 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106799
       have i₂ := eq106250
       grind)
    | exact superpose eq106250 eq106799
    | exact resolve eq106799 eq106250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106799
  have eq106803 : x = (M.op x y) := by grind
  clear eq106802
  have eq106807 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq106803 eq20
    | exact resolve eq20 eq106803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq106809 : x ≠ y ∨ x = (k x y) := by
    first
    | exact superpose eq106803 eq50
    | exact resolve eq50 eq106803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq106803
  have eq107105 : x = (k x y) := by
    first
    | (have r₁ := eq106809
       have r₂ := eq106250
       grind)
    | exact resolve eq106809 eq106250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106809
  have eq107107 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq106807
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq106807
    | exact resolve eq106807 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106807
  have eq107163 : x = (k x x) := by
    first
    | (have i₁ := eq107105
       have i₂ := eq106250
       grind)
    | exact superpose eq106250 eq107105
    | exact resolve eq107105 eq106250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106250 eq107105
  have eq107459 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq107107 eq106534
    | exact resolve eq106534 eq107107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106534
  have eq107499 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2961 x
       have i₂ := eq107163
       grind)
    | exact superpose eq107163 eq2961
    | (have j0 := eq2961 x
       grind)
    | exact resolve eq2961 eq107163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2961 eq107163
  have eq107503 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq107499
  have eq107508 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq107503
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq107503
    | exact resolve eq107503 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq107503
  have eq107524 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq107107 eq107508
    | exact resolve eq107508 eq107107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107107 eq107508
  have eq107539 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq107459 eq107524
    | exact resolve eq107524 eq107459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107459 eq107524
  have eq107552 : False := by grind
  exact eq107552

/-- `x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then m(Y,X) else if m(X,Y) = X then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxy_y_pyx_x_pxy_x_pyx_pyx_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq16
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq16
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq16
    | exact resolve eq16 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq45
    | exact resolve eq45 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq48
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq60
    | exact resolve eq60 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq73
    | exact resolve eq73 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq177 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq973 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq974 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq975 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq980 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq14
    | (have j0 := eq14 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq982 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq986 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq980 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq980 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq980 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq980 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq980 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq989 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq986 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq986 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq986 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | exact resolve eq986 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq6486 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq974
       grind)
    | exact superpose eq974 eq41
    | exact resolve eq41 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6487 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6486
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6486
    | exact resolve eq6486 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6486
  have eq6491 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq6487
    | exact resolve eq6487 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6487
  have eq6751 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq989 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq989
    | (have j0 := eq989 (σ X0) (σ X1)
       grind)
    | exact resolve eq989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10500 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq982 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq982
    | (have j0 := eq982 (σ X0) (σ X1)
       grind)
    | exact resolve eq982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15366 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6491 eq975
    | exact resolve eq975 eq6491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15383 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15366
       have r₂ := eq27
       grind)
    | exact resolve eq15366 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15366
  have eq15390 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15383 eq28
    | (have r₁ := eq28 (σ x) (σ y)
       have r₂ := eq15383
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq15383
       grind)
    | (have r₁ := eq28 x y
       have r₂ := eq15383
       grind)
    | exact resolve eq28 eq15383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15383
  have eq15393 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15390
  have eq15439 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15393 eq153
    | exact resolve eq153 eq15393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq15393
  have eq15448 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq15439
    | exact resolve eq15439 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15439
  have eq15453 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq974 eq15448
    | exact resolve eq15448 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15448
  have eq15454 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15453
  have eq15461 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq15454
       grind)
    | exact superpose eq15454 eq28
    | (have r₁ := eq28 x y
       have r₂ := eq15454
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq15454
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq15454
       grind)
    | exact resolve eq28 eq15454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15462 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq15454
       grind)
    | exact superpose eq15454 eq14
    | (have j0 := eq14 y x
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq15454
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq15454
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq15454
       grind)
    | exact resolve eq14 eq15454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15463 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15462
  have eq15464 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15461
  have eq15465 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15463
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15463
    | exact resolve eq15463 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15463
  have eq15467 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15465
       have r₂ := eq177
       grind)
    | exact resolve eq15465 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15465
  have eq15473 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq15467
       grind)
    | exact superpose eq15467 eq40
    | exact resolve eq40 eq15467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15467
  have eq15480 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15473
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15473
    | exact resolve eq15473 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15473
  have eq15485 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq15480
    | exact resolve eq15480 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15480
  have eq15517 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq15464
       grind)
    | exact superpose eq15464 eq41
    | exact resolve eq41 eq15464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15464
  have eq15524 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15517
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15517
    | exact resolve eq15517 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15517
  have eq15534 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15524 eq975
    | exact resolve eq975 eq15524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15524
  have eq15543 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15534
  have eq16347 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15543 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq15543
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq15543
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq15543
       grind)
    | exact resolve eq14 eq15543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15543
  have eq16348 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16347
  have eq16350 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq16348
    | exact resolve eq16348 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16348
  have eq16352 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16350
       have r₂ := eq178
       grind)
    | exact resolve eq16350 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16350
  have eq16354 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16352 eq15485
    | exact resolve eq15485 eq16352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15485
  have eq16357 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16352 eq115
    | exact resolve eq115 eq16352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq16352
  have eq16365 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16354
  have eq16372 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16365
       have r₂ := eq27
       grind)
    | exact resolve eq16365 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16365
  have eq16376 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16372 eq178
    | (have r₁ := eq178
       have r₂ := eq16372
       grind)
    | exact resolve eq178 eq16372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16372
  have eq16379 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16376
  have eq16391 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16379 eq142
    | exact resolve eq142 eq16379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16379
  have eq16406 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq16391
    | exact resolve eq16391 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16391
  have eq16430 : y ≠ y ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq982 y x
       have i₂ := eq16406
       grind)
    | exact superpose eq16406 eq982
    | (have j0 := eq982 y x
       grind)
    | (have r₁ := eq982 y x
       have r₂ := eq16406
       grind)
    | exact resolve eq982 eq16406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16432 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16430
  have eq16440 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16432
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16432
    | exact resolve eq16432 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16432
  have eq16441 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16440
  have eq16946 : y ≠ y ∨ y = (M.op x y) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq16441
       grind)
    | exact superpose eq16441 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq16441
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq16441
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq16441
       grind)
    | exact resolve eq12 eq16441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16949 : x ≠ y ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16441
  have eq16950 : y = (M.op x y) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16946
  have eq16954 : y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16950
       have r₂ := eq16949
       grind)
    | exact resolve eq16950 eq16949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16950
  have eq16958 : y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16954
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16954
    | exact resolve eq16954 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16954
  have eq16959 : y = (M.op x y) ∨ x = (k y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16958
  have eq16961 : y = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16357 eq16959
    | exact resolve eq16959 eq16357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16357 eq16959
  have eq16962 : y = (M.op x y) ∨ x = (τ (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15454 eq16961
    | exact resolve eq16961 eq15454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15454 eq16961
  have eq16963 : x = y ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq16962
    | exact resolve eq16962 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16962
  have eq16964 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16963
       have r₂ := eq16949
       grind)
    | exact resolve eq16963 eq16949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16949 eq16963
  have eq16968 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq16964
       grind)
    | exact superpose eq16964 eq14
    | (have j0 := eq14 y x
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq16964
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq16964
       grind)
    | exact resolve eq14 eq16964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16964
  have eq16969 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16968
  have eq16972 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16969
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16969
    | exact resolve eq16969 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16969
  have eq16974 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16972
       have r₂ := eq177
       grind)
    | exact resolve eq16972 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16972
  have eq16982 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16406
       have i₂ := eq16974
       grind)
    | exact superpose eq16974 eq16406
    | exact resolve eq16406 eq16974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16406 eq16974
  have eq16991 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq16982
  have eq17031 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16991 eq973
    | (have r₁ := eq973
       have r₂ := eq16991
       grind)
    | exact resolve eq973 eq16991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq17033 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16991 eq178
    | exact resolve eq178 eq16991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17034 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16991 eq27
    | exact resolve eq27 eq16991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17035 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17031
  have eq20454 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17035 eq91
    | exact resolve eq91 eq17035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq20479 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq20454
    | exact resolve eq20454 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20454
  have eq20712 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20479 eq28
    | (have r₁ := eq28 (σ x) (σ y)
       have r₂ := eq20479
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq20479
       grind)
    | exact resolve eq28 eq20479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20713 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20479 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq20479
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq20479
       grind)
    | exact resolve eq14 eq20479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20479
  have eq20714 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq20713
  have eq20715 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq20712
  have eq20718 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq20714
    | exact resolve eq20714 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20714
  have eq20720 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16991 eq20718
    | exact resolve eq20718 eq16991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20718
  have eq20722 : (σ x) = (k (σ y) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20720
       have r₂ := eq17033
       grind)
    | exact resolve eq20720 eq17033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17033 eq20720
  have eq20739 : (τ (σ x)) = (k y (τ (σ x))) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20722 eq108
    | exact resolve eq108 eq20722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq20722
  have eq20769 : y = (k x y) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq20739
    | exact resolve eq20739 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20739
  have eq20818 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq974
       have i₂ := eq20769
       grind)
    | exact superpose eq20769 eq974
    | exact resolve eq974 eq20769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20828 : y ≠ y ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq989 x y
       have i₂ := eq20769
       grind)
    | exact superpose eq20769 eq989
    | (have j0 := eq989 y x
       grind)
    | (have r₁ := eq989 x y
       have r₂ := eq20769
       grind)
    | (have r₁ := eq989 y x
       have r₂ := eq20769
       grind)
    | exact resolve eq989 eq20769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20769
  have eq20829 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq20828
  have eq20833 : x = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20818
  have eq20839 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20829
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20829
    | exact resolve eq20829 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20829
  have eq20840 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (k y x) ∨ y = (M.op x y) := by grind
  clear eq20839
  have eq20852 : x = (k y x) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20833 eq20840
    | exact resolve eq20840 eq20833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20833 eq20840
  have eq20887 : x ≠ x ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq989 y x
       have i₂ := eq20852
       grind)
    | exact superpose eq20852 eq989
    | (have j0 := eq989 x y
       grind)
    | (have r₁ := eq989 y x
       have r₂ := eq20852
       grind)
    | exact resolve eq989 eq20852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20852
  have eq20888 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq20887
  have eq20902 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20888
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20888
    | exact resolve eq20888 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20888
  have eq20903 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq20902
  have eq22245 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6491 eq20715
    | exact resolve eq20715 eq6491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6491 eq20715
  have eq22273 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq22245
  have eq22281 : (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq22273
       have r₂ := eq17034
       grind)
    | exact resolve eq22273 eq17034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17034 eq22273
  have eq22283 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq22281
       have r₂ := eq972
       grind)
    | exact resolve eq22281 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22281
  have eq22289 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq974
       have i₂ := eq22283
       grind)
    | exact superpose eq22283 eq974
    | exact resolve eq974 eq22283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974 eq22283
  have eq22308 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq22289
  have eq22342 : x = y ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20903
       have i₂ := eq22308
       grind)
    | exact superpose eq22308 eq20903
    | exact resolve eq20903 eq22308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20903
  have eq22343 : x ≠ x ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq22308
       grind)
    | exact superpose eq22308 eq28
    | (have r₁ := eq28 x y
       have r₂ := eq22308
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq22308
       grind)
    | exact resolve eq28 eq22308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22344 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq22308
       grind)
    | exact superpose eq22308 eq14
    | (have j0 := eq14 y x
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq22308
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq22308
       grind)
    | exact resolve eq14 eq22308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22308
  have eq22345 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq22344
  have eq22346 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq22343
  have eq22347 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq22342
  have eq22352 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22345
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22345
    | exact resolve eq22345 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22345
  have eq22354 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq22352
       have r₂ := eq177
       grind)
    | exact resolve eq22352 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22352
  have eq22370 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq22354
       grind)
    | exact superpose eq22354 eq40
    | exact resolve eq40 eq22354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22354
  have eq22393 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22370
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22370
    | exact resolve eq22370 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22370
  have eq22401 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq22393
    | exact resolve eq22393 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22393
  have eq22473 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22347 eq32
    | exact resolve eq32 eq22347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22347
  have eq22631 : x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq22473
    | exact resolve eq22473 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22473
  have eq22632 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq22631
  have eq22639 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq22632
       grind)
    | exact superpose eq22632 eq24
    | exact resolve eq24 eq22632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22643 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq177
       have i₂ := eq22632
       grind)
    | exact superpose eq22632 eq177
    | (have r₁ := eq177
       have r₂ := eq22632
       grind)
    | exact resolve eq177 eq22632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22632
  have eq22670 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq22643
  have eq22693 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq22639
    | exact resolve eq22639 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22639
  have eq22965 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22670 eq40
    | exact resolve eq40 eq22670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22967 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22670 eq10500
    | (have j0 := eq10500 (M.op x y) x
       grind)
    | exact resolve eq10500 eq22670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10500 eq22670
  have eq22973 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq22967
  have eq22977 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq22973
    | exact resolve eq22973 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22973
  have eq22979 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq22965
    | exact resolve eq22965 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22965
  have eq22984 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq22977
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22977
    | exact resolve eq22977 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22977
  have eq22986 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22693 eq22979
    | exact resolve eq22979 eq22693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22979
  have eq22991 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq22984
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22984
    | exact resolve eq22984 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22984
  have eq22997 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq22991
    | exact resolve eq22991 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22991
  have eq23000 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq22997
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22997
    | exact resolve eq22997 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22997
  have eq23003 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq23000
    | exact resolve eq23000 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23000
  have eq23007 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22693 eq23003
    | exact resolve eq23003 eq22693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23003
  have eq23009 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22693 eq23007
    | exact resolve eq23007 eq22693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23007
  have eq23010 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22693 eq23009
    | exact resolve eq23009 eq22693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23009
  have eq23011 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq23010
    | exact resolve eq23010 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23010
  have eq23718 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq22346
       grind)
    | exact superpose eq22346 eq41
    | exact resolve eq41 eq22346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22346
  have eq23736 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23718
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23718
    | exact resolve eq23718 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23718
  have eq23758 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23736 eq17035
    | exact resolve eq17035 eq23736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17035 eq23736
  have eq23773 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23758
  have eq23839 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23773 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq23773
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq23773
       grind)
    | exact resolve eq14 eq23773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23773
  have eq23840 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23839
  have eq23844 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq23840
    | exact resolve eq23840 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23840
  have eq23846 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22401 eq23844
    | exact resolve eq23844 eq22401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22401 eq23844
  have eq23848 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23846
       have r₂ := eq27
       grind)
    | exact resolve eq23846 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23846
  have eq33107 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq23011 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq23011
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq23011
       grind)
    | exact resolve eq12 eq23011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33110 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq23011
  have eq33111 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq33107
  have eq33121 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq33111
       have r₂ := eq33110
       grind)
    | exact resolve eq33111 eq33110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33111
  have eq33124 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq33121
    | exact resolve eq33121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33121
  have eq33125 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq33124
  have eq33127 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22986 eq33125
    | exact resolve eq33125 eq22986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33125
  have eq33129 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq33127
       have r₂ := eq33110
       grind)
    | exact resolve eq33127 eq33110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33110 eq33127
  have eq33145 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq33129 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq33129
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq33129
       grind)
    | exact resolve eq14 eq33129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33129
  have eq33146 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq33145
  have eq33155 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq33146
    | exact resolve eq33146 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33146
  have eq33159 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq33155
       have r₂ := eq178
       grind)
    | exact resolve eq33155 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33155
  have eq33160 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq22986 eq33159
    | exact resolve eq33159 eq22986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22986 eq33159
  have eq33162 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq33160 eq27
    | exact resolve eq27 eq33160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33160
  have eq33170 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq33162
       have r₂ := eq22693
       grind)
    | exact resolve eq33162 eq22693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22693 eq33162
  have eq33171 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq33170
       grind)
    | exact superpose eq33170 eq18
    | exact resolve eq18 eq33170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33172 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq33170
       grind)
    | exact superpose eq33170 eq22
    | exact resolve eq22 eq33170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33190 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq972
       have i₂ := eq33170
       grind)
    | exact superpose eq33170 eq972
    | (have r₁ := eq972
       have r₂ := eq33170
       grind)
    | exact resolve eq972 eq33170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq33193 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = y := by grind
  clear eq33190
  have eq33215 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq33172
    | exact resolve eq33172 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33172
  have eq33420 : y ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq33171 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq33171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33783 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq33193 eq28
    | (have r₁ := eq28 (M.op x y) y
       have r₂ := eq33193
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq33193
       grind)
    | exact resolve eq28 eq33193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33784 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq33193 eq14
    | (have j0 := eq14 y (M.op x y)
       grind)
    | (have r₁ := eq14 y (M.op x y)
       have r₂ := eq33193
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq33193
       grind)
    | exact resolve eq14 eq33193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33193
  have eq33785 : (k y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = y := by grind
  clear eq33784
  have eq33786 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = y := by grind
  clear eq33783
  have eq33787 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq33171 eq33785
    | exact resolve eq33785 eq33171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33785
  have eq33789 : (M.op x y) = (k y (M.op x y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | (have r₁ := eq33787
       have r₂ := eq33420
       grind)
    | exact resolve eq33787 eq33420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33420 eq33787
  have eq33797 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq33789 eq37
    | exact resolve eq37 eq33789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq33801 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq33789 eq6751
    | (have j0 := eq6751 (M.op x y) y
       grind)
    | exact resolve eq6751 eq33789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6751 eq33789
  have eq33807 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ x = y := by grind
  clear eq33801
  have eq33816 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq33807
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33807
    | exact resolve eq33807 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33807
  have eq33820 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq20 eq33797
    | exact resolve eq33797 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33797
  have eq33826 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq20 eq33816
    | exact resolve eq33816 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33816
  have eq33830 : (σ x) = (k (σ y) (σ x)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq33215 eq33820
    | exact resolve eq33820 eq33215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33820
  have eq33835 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq20 eq33826
    | exact resolve eq33826 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33826
  have eq33841 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq33835
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33835
    | exact resolve eq33835 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33835
  have eq33844 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq33215 eq33841
    | exact resolve eq33841 eq33215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33841
  have eq33847 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq33215 eq33844
    | exact resolve eq33844 eq33215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33844
  have eq33850 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq26 eq33847
    | exact resolve eq33847 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33847
  have eq36468 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq33786 eq41
    | exact resolve eq41 eq33786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq33786
  have eq36486 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq20 eq36468
    | exact resolve eq36468 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36468
  have eq36493 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq33215 eq36486
    | exact resolve eq36486 eq33215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36486
  have eq36597 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq33850 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq33850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36614 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq26 eq36597
    | exact resolve eq36597 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36597
  have eq36615 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq33830 eq36614
    | exact resolve eq36614 eq33830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36614
  have eq36616 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by grind
  clear eq36615
  have eq36632 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq36493 eq975
    | exact resolve eq975 eq36493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36493
  have eq36652 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = y := by grind
  clear eq36632
  have eq36667 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16991 eq36652
    | exact resolve eq36652 eq16991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36652
  have eq36668 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) := by grind
  clear eq36667
  have eq38653 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq36668 eq33850
    | exact resolve eq33850 eq36668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33850 eq36668
  have eq38658 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq38653
  have eq38668 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq38658
       have r₂ := eq36616
       grind)
    | exact resolve eq38658 eq36616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36616 eq38658
  have eq38672 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16991 eq38668
    | exact resolve eq38668 eq16991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38668
  have eq38673 : y = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq38672
  have eq38684 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38673 eq38
    | exact resolve eq38 eq38673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq38673
  have eq38710 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38684
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38684
    | exact resolve eq38684 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38684
  have eq38737 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq33215 eq38710
    | exact resolve eq38710 eq33215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38710
  have eq38797 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16991 eq38737
    | exact resolve eq38737 eq16991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38737
  have eq38798 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq38797
  have eq38822 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38798 eq975
    | exact resolve eq975 eq38798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq38838 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38798 eq989
    | (have j0 := eq989 (σ y) (σ x)
       grind)
    | (have r₁ := eq989 (σ x) (σ y)
       have r₂ := eq38798
       grind)
    | exact resolve eq989 eq38798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989 eq38798
  have eq38839 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq38838
  have eq38851 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq38822
  have eq38862 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq38839
    | exact resolve eq38839 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38839
  have eq38863 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq38862
  have eq38874 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38851 eq38863
    | exact resolve eq38863 eq38851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38863
  have eq38883 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38874 eq178
    | (have r₁ := eq178
       have r₂ := eq38874
       grind)
    | exact resolve eq178 eq38874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38874
  have eq38887 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq38883
  have eq38905 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38851 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq38851
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq38851
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq38851
       grind)
    | exact resolve eq14 eq38851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38851
  have eq38906 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq38905
  have eq38917 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq38906
    | exact resolve eq38906 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38906
  have eq38922 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq38917
       have r₂ := eq178
       grind)
    | exact resolve eq38917 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq38917
  have eq38949 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38922 eq33830
    | exact resolve eq33830 eq38922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33830 eq38922
  have eq38958 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq38949
  have eq38980 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16991 eq38958
    | exact resolve eq38958 eq16991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16991 eq38958
  have eq38981 : y = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq38980
  have eq39345 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38887 eq142
    | exact resolve eq142 eq38887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq38887
  have eq39381 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq39345
    | exact resolve eq39345 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39345
  have eq39389 : y = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23848 eq39381
    | exact resolve eq39381 eq23848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39381
  have eq39454 : y ≠ y ∨ y = (M.op (M.op x y) y) ∨ y = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39389 eq982
    | (have j0 := eq982 y (M.op x y)
       grind)
    | (have r₁ := eq982 y (M.op x y)
       have r₂ := eq39389
       grind)
    | exact resolve eq982 eq39389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq39456 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq39454
  have eq177194 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39456 eq28
    | (have r₁ := eq28 (M.op x y) y
       have r₂ := eq39456
       grind)
    | (have r₁ := eq28 y (M.op x y)
       have r₂ := eq39456
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq39456
       grind)
    | exact resolve eq28 eq39456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq39456
  have eq177198 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq177194
  have eq177201 : y = (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38981 eq177198
    | exact resolve eq177198 eq38981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177198
  have eq177202 : y = (M.op (M.op x y) y) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq177201
  have eq177211 : y ≠ y ∨ (k (M.op x y) y) = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq177202 eq14
    | (have j0 := eq14 (M.op x y) y
       grind)
    | (have r₁ := eq14 (M.op x y) y
       have r₂ := eq177202
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq177202
       grind)
    | exact resolve eq14 eq177202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177202
  have eq177212 : (k (M.op x y) y) = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq177211
  have eq177218 : y = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38981 eq177212
    | exact resolve eq177212 eq38981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38981 eq177212
  have eq177219 : y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq177218
  have eq177231 : y ≠ y ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq177219 eq12
    | (have j0 := eq12 y (M.op x y)
       grind)
    | (have r₁ := eq12 y (M.op x y)
       have r₂ := eq177219
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq177219
       grind)
    | exact resolve eq12 eq177219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177219
  have eq177234 : y ≠ y ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq177231
  have eq177235 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq177234
  have eq177241 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39389 eq177235
    | exact resolve eq177235 eq39389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39389 eq177235
  have eq177242 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq177241
  have eq177247 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq177242 eq33171
    | exact resolve eq33171 eq177242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33171 eq177242
  have eq177252 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq177247
  have eq177257 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23848 eq177252
    | exact resolve eq177252 eq23848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177252
  have eq177258 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq177257
  have eq177265 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq177258 eq27
    | exact resolve eq27 eq177258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177258
  have eq177276 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq33215 eq177265
    | (have r₁ := eq177265
       have r₂ := eq33215
       grind)
    | exact resolve eq177265 eq33215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33215 eq177265
  have eq177278 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq177276
  have eq177279 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23848 eq177278
    | exact resolve eq177278 eq23848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23848 eq177278
  have eq177280 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq177279
  have eq177282 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq177280 eq32
    | exact resolve eq32 eq177280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq177280
  have eq177679 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq177282
    | exact resolve eq177282 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq177282
  have eq177743 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq177679
  have eq177749 : x = y := by
    first
    | (have r₁ := eq177743
       have r₂ := eq33170
       grind)
    | exact resolve eq177743 eq33170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33170 eq177743
  have eq177781 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq177749
       grind)
    | exact superpose eq177749 eq18
    | exact resolve eq18 eq177749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq177782 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq177749
       grind)
    | exact superpose eq177749 eq24
    | exact resolve eq24 eq177749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq177786 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq177
       have i₂ := eq177749
       grind)
    | exact superpose eq177749 eq177
    | exact resolve eq177 eq177749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq177749
  have eq177933 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq177782
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq177782
    | exact resolve eq177782 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177782
  have eq177934 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq177933 eq26
    | exact resolve eq26 eq177933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq177933
  have eq178296 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq177781
       grind)
    | exact superpose eq177781 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq177781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177781
  have eq178301 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq178296
  have eq178309 : (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq178301
       have r₂ := eq177786
       grind)
    | exact resolve eq178301 eq177786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177786 eq178301
  have eq179840 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq177934 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq177934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179843 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq177934 eq14
    | exact resolve eq14 eq177934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177934
  have eq179845 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq179840
  have eq179851 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq179845
       have r₂ := eq179843
       grind)
    | exact resolve eq179845 eq179843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179843 eq179845
  have eq179886 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq178309
       grind)
    | exact superpose eq178309 eq40
    | exact resolve eq40 eq178309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq178309
  have eq179927 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq179886
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq179886
    | exact resolve eq179886 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq179886
  have eq179939 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq179851 eq179927
    | exact resolve eq179927 eq179851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179851 eq179927
  have eq179947 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq179939
    | exact resolve eq179939 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq179939
  have eq179955 : False := by grind
  exact eq179955

/-- `x □ y = if m(X,Y) = Y then m(X,Y) else if m(Y,X) = Y then X else if m(Y,X) = X then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxy_y_pyx_y_pyx_x_pxy_x_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq16
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq16
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq45
    | exact resolve eq45 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq48
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq60
    | exact resolve eq60 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq175 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq974 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq975 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq978 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq981 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq982 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq986 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq978 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq978 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq978 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq978 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq978 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq989 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq986 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq986 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | (have r₁ := eq986 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq986 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq2359 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq974
       grind)
    | exact superpose eq974 eq40
    | exact resolve eq40 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2360 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2359
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2359
    | exact resolve eq2359 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2359
  have eq2362 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq2360
    | exact resolve eq2360 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq6380 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq981 (σ X1) (σ X0)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq981
    | (have j0 := eq981 (σ X1) (σ X0)
       grind)
    | exact resolve eq981 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6386 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq982 (σ X1) (σ X0)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq982
    | (have j0 := eq982 (σ X1) (σ X0)
       grind)
    | exact resolve eq982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq6634 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq989 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq989
    | (have j0 := eq989 (σ X0) (σ X1)
       grind)
    | exact resolve eq989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq15388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2362 eq975
    | exact resolve eq975 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15401 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq15388
       have r₂ := eq27
       grind)
    | exact resolve eq15388 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15388
  have eq15412 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq15401 eq14
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq15401
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq15401
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq15401
       grind)
    | exact resolve eq14 eq15401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15401
  have eq15413 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq15412
  have eq15426 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq15413 eq108
    | exact resolve eq108 eq15413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq15413
  have eq15436 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq15426
    | exact resolve eq15426 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15426
  have eq15441 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq974 eq15436
    | exact resolve eq15436 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15436
  have eq15442 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15441
  have eq15450 : x ≠ x ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq15442
       grind)
    | exact superpose eq15442 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | (have r₁ := eq28 x y
       have r₂ := eq15442
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq15442
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq15442
       grind)
    | exact resolve eq28 eq15442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15452 : x ≠ x ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq15442
       grind)
    | exact superpose eq15442 eq14
    | (have r₁ := eq14 y x
       have r₂ := eq15442
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq15442
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq15442
       grind)
    | exact resolve eq14 eq15442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15453 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15452
  have eq15454 : x = y ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15450
  have eq15457 : (M.op x y) = (k x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15454
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15454
    | exact resolve eq15454 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15454
  have eq15458 : (M.op x y) = (k x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15457
       have r₂ := eq175
       grind)
    | exact resolve eq15457 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15457
  have eq15463 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq15453
       grind)
    | exact superpose eq15453 eq37
    | exact resolve eq37 eq15453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15453
  have eq15471 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15463
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15463
    | exact resolve eq15463 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15463
  have eq15478 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq15458
       grind)
    | exact superpose eq15458 eq41
    | exact resolve eq41 eq15458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15458
  have eq15483 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15478
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15478
    | exact resolve eq15478 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15478
  have eq15488 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq15483
    | exact resolve eq15483 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15483
  have eq15495 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15471 eq975
    | exact resolve eq975 eq15471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975 eq15471
  have eq15503 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15495
  have eq15542 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15503 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | (have r₁ := eq28 (σ x) (σ y)
       have r₂ := eq15503
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq15503
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq15503
       grind)
    | exact resolve eq28 eq15503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15503
  have eq15546 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15542
  have eq15549 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15546
    | exact resolve eq15546 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15546
  have eq15550 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15549
       have r₂ := eq176
       grind)
    | exact resolve eq15549 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15549
  have eq15552 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15550 eq15488
    | exact resolve eq15488 eq15550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15488
  have eq15555 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15550 eq99
    | exact resolve eq99 eq15550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq15550
  have eq15561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq15552
  have eq15568 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15561
       have r₂ := eq27
       grind)
    | exact resolve eq15561 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15561
  have eq16440 : y ≠ (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq981 y x
       have i₂ := eq15555
       grind)
    | exact superpose eq15555 eq981
    | (have j0 := eq981 y x
       grind)
    | exact resolve eq981 eq15555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16443 : y = (M.op x y) ∨ y ≠ (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16440
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16440
    | exact resolve eq16440 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16440
  have eq16444 : y = (M.op x y) ∨ y ≠ (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16443
  have eq16454 : y = (M.op x y) ∨ y ≠ (τ (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15442 eq16444
    | exact resolve eq16444 eq15442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16444
  have eq16460 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16454
       have r₂ := eq32
       grind)
    | exact resolve eq16454 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16454
  have eq16472 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15568 eq176
    | (have r₁ := eq176
       have r₂ := eq15568
       grind)
    | exact resolve eq176 eq15568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15568
  have eq16475 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq16472
  have eq16492 : (τ (σ y)) = (k x (τ (σ y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16475 eq91
    | exact resolve eq91 eq16475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16475
  have eq16506 : y = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq16492
    | exact resolve eq16492 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16492
  have eq16978 : y ≠ y ∨ y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq16460
       grind)
    | exact superpose eq16460 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16460
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq16460
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16460
       grind)
    | exact resolve eq13 eq16460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16980 : x ≠ y ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16460
  have eq16981 : y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16978
  have eq16985 : y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16981
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16981
    | exact resolve eq16981 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16981
  have eq16986 : y = (M.op x y) ∨ x = (k x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16985
  have eq16988 : y = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15555 eq16986
    | exact resolve eq16986 eq15555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15555 eq16986
  have eq16989 : y = (M.op x y) ∨ x = (τ (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15442 eq16988
    | exact resolve eq16988 eq15442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15442 eq16988
  have eq16990 : x = y ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq16989
    | exact resolve eq16989 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16989
  have eq16991 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16990
       have r₂ := eq16980
       grind)
    | exact resolve eq16990 eq16980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16980 eq16990
  have eq16994 : x ≠ x ∨ x = y ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq16991
       grind)
    | exact superpose eq16991 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | (have r₁ := eq28 x y
       have r₂ := eq16991
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq16991
       grind)
    | exact resolve eq28 eq16991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16991
  have eq16998 : x = y ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16994
  have eq17002 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16998
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16998
    | exact resolve eq16998 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16998
  have eq17003 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17002
       have r₂ := eq175
       grind)
    | exact resolve eq17002 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17002
  have eq17036 : y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16506
       have i₂ := eq17003
       grind)
    | exact superpose eq17003 eq16506
    | exact resolve eq16506 eq17003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16506 eq17003
  have eq17049 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq17036
  have eq17091 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17049 eq178
    | (have r₁ := eq178
       have r₂ := eq17049
       grind)
    | exact resolve eq178 eq17049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq17093 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17049 eq27
    | exact resolve eq27 eq17049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17094 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq17091
  have eq17182 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17094 eq142
    | exact resolve eq142 eq17094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq17208 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32 eq17182
    | exact resolve eq17182 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17182
  have eq17219 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17208 eq14
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq17208
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq17208
       grind)
    | exact resolve eq14 eq17208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17208
  have eq17220 : (σ x) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq17219
  have eq17234 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17220 eq2362
    | exact resolve eq2362 eq17220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362 eq17220
  have eq17245 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17234
  have eq17252 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17245
       have r₂ := eq17093
       grind)
    | exact resolve eq17245 eq17093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17245
  have eq17258 : y = (k y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17252
       have r₂ := eq177
       grind)
    | exact resolve eq17252 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17252
  have eq17267 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq974
       have i₂ := eq17258
       grind)
    | exact superpose eq17258 eq974
    | exact resolve eq974 eq17258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974 eq17258
  have eq17283 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17267
  have eq17321 : x ≠ x ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq17283
       grind)
    | exact superpose eq17283 eq28
    | (have j0 := eq28 y x
       grind)
    | (have r₁ := eq28 x y
       have r₂ := eq17283
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq17283
       grind)
    | exact resolve eq28 eq17283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17323 : x ≠ x ∨ x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq17283
       grind)
    | exact superpose eq17283 eq14
    | (have r₁ := eq14 y x
       have r₂ := eq17283
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq17283
       grind)
    | exact resolve eq14 eq17283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17283
  have eq17324 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17323
  have eq17325 : x ≠ x ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq17321
  have eq17326 : x = y ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq17325
  have eq17328 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17326
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17326
    | exact resolve eq17326 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17326
  have eq17329 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17328
       have r₂ := eq175
       grind)
    | exact resolve eq17328 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17328
  have eq17553 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq17329
       grind)
    | exact superpose eq17329 eq41
    | exact resolve eq41 eq17329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17329
  have eq17568 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17553
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17553
    | exact resolve eq17553 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17553
  have eq17576 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq17568
    | exact resolve eq17568 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17568
  have eq17639 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq17324
       grind)
    | exact superpose eq17324 eq37
    | exact resolve eq37 eq17324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq17324
  have eq17654 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17639
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17639
    | exact resolve eq17639 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17639
  have eq17669 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17654 eq17094
    | exact resolve eq17094 eq17654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17094 eq17654
  have eq17678 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17669
  have eq17696 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17678 eq28
    | (have j0 := eq28 y x
       grind)
    | (have r₁ := eq28 (σ x) (σ y)
       have r₂ := eq17678
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq17678
       grind)
    | exact resolve eq28 eq17678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17678
  have eq17700 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17696
  have eq17701 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17700
  have eq17704 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17701
    | exact resolve eq17701 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17701
  have eq17705 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17049 eq17704
    | exact resolve eq17704 eq17049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17049 eq17704
  have eq17720 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17705 eq17576
    | exact resolve eq17576 eq17705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17705
  have eq17734 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq17720
  have eq17749 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17734
       have r₂ := eq17093
       grind)
    | exact resolve eq17734 eq17093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17093 eq17734
  have eq17760 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq17749 eq32
    | exact resolve eq32 eq17749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17749
  have eq17871 : x = y ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq17760
    | exact resolve eq17760 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17760
  have eq17872 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq17871
  have eq17874 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq17872
       grind)
    | exact superpose eq17872 eq24
    | exact resolve eq24 eq17872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17877 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq175
       have i₂ := eq17872
       grind)
    | exact superpose eq17872 eq175
    | (have r₁ := eq175
       have r₂ := eq17872
       grind)
    | exact resolve eq175 eq17872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17872
  have eq17903 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq17877
  have eq17923 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq17874
    | exact resolve eq17874 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17874
  have eq18043 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17903 eq36
    | exact resolve eq36 eq17903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq18046 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17903 eq6380
    | (have j0 := eq6380 x (M.op x y)
       grind)
    | exact resolve eq6380 eq17903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17903
  have eq18050 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq18046
  have eq18051 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18050
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18050
    | exact resolve eq18050 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18050
  have eq18054 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq18043
    | exact resolve eq18043 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18043
  have eq18057 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq18051
    | exact resolve eq18051 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18051
  have eq18060 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17923 eq18054
    | exact resolve eq18054 eq17923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18054
  have eq18063 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18057
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18057
    | exact resolve eq18057 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18057
  have eq18068 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq18063
    | exact resolve eq18063 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18063
  have eq18070 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq18068
    | exact resolve eq18068 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18068
  have eq18072 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18070
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18070
    | exact resolve eq18070 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18070
  have eq18074 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17923 eq18072
    | exact resolve eq18072 eq17923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18072
  have eq18076 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq18074
    | exact resolve eq18074 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18074
  have eq18078 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17923 eq18076
    | exact resolve eq18076 eq17923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18076
  have eq18080 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17923 eq18078
    | exact resolve eq18078 eq17923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17923 eq18078
  have eq21074 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18080 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18080
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18080
       grind)
    | exact resolve eq13 eq18080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21076 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq18080
  have eq21077 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq21074
  have eq21085 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq21077
    | exact resolve eq21077 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21077
  have eq21086 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq21085
  have eq21087 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18060 eq21086
    | exact resolve eq21086 eq18060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18060 eq21086
  have eq21088 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq21087
       have r₂ := eq21076
       grind)
    | exact resolve eq21087 eq21076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21076 eq21087
  have eq21097 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21088 eq28
    | (have j0 := eq28 y x
       grind)
    | (have r₁ := eq28 (σ x) (σ y)
       have r₂ := eq21088
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq21088
       grind)
    | exact resolve eq28 eq21088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21088
  have eq21101 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq21097
  have eq21111 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq21101
    | exact resolve eq21101 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21101
  have eq21112 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq21111
       have r₂ := eq176
       grind)
    | exact resolve eq21111 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21111
  have eq21113 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17576 eq21112
    | exact resolve eq21112 eq17576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17576 eq21112
  have eq21114 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq21113
       have r₂ := eq27
       grind)
    | exact resolve eq21113 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21113
  have eq21116 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21114 eq32
    | exact resolve eq32 eq21114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21238 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq21116
    | exact resolve eq21116 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21116
  have eq21239 : x = (M.op x y) ∨ x = y := by grind
  clear eq21238
  have eq21287 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq21239
       grind)
    | exact superpose eq21239 eq18
    | exact resolve eq18 eq21239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21288 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq21239
       grind)
    | exact superpose eq21239 eq22
    | exact resolve eq22 eq21239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21291 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq177
       have i₂ := eq21239
       grind)
    | exact superpose eq21239 eq177
    | (have r₁ := eq177
       have r₂ := eq21239
       grind)
    | exact resolve eq177 eq21239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq21309 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (k y (M.op x y)) ∨ x = y := by grind
  clear eq21291
  have eq21327 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq21288
    | exact resolve eq21288 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21288
  have eq21467 : y ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq21287 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq21287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21749 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq21309 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | (have r₁ := eq28 (M.op x y) y
       have r₂ := eq21309
       grind)
    | exact resolve eq28 eq21309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21751 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq21309 eq14
    | (have r₁ := eq14 y (M.op x y)
       have r₂ := eq21309
       grind)
    | exact resolve eq14 eq21309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21309
  have eq21752 : (M.op x y) = (k y (M.op x y)) ∨ y = (k y (M.op x y)) ∨ x = y := by grind
  clear eq21751
  have eq21753 : y = (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) ∨ y = (k y (M.op x y)) ∨ x = y := by grind
  clear eq21749
  have eq21755 : y = (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq21287 eq21753
    | exact resolve eq21753 eq21287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21753
  have eq21757 : (M.op x y) = (k (M.op x y) y) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | (have r₁ := eq21755
       have r₂ := eq21467
       grind)
    | exact resolve eq21755 eq21467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21755
  have eq21993 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq21752 eq6380
    | (have j0 := eq6380 y (M.op x y)
       grind)
    | exact resolve eq6380 eq21752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6380 eq21752
  have eq21998 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k y (M.op x y)) ∨ x = y := by grind
  clear eq21993
  have eq22004 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq21998
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21998
    | exact resolve eq21998 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21998
  have eq22010 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20 eq22004
    | exact resolve eq22004 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22004
  have eq22016 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq22010
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22010
    | exact resolve eq22010 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22010
  have eq22021 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20 eq22016
    | exact resolve eq22016 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22016
  have eq22023 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20 eq22021
    | exact resolve eq22021 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22021
  have eq22025 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq22023
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22023
    | exact resolve eq22023 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22023
  have eq22027 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq21327 eq22025
    | exact resolve eq22025 eq21327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22025
  have eq22029 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq21327 eq22027
    | exact resolve eq22027 eq21327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22027
  have eq22031 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq26 eq22029
    | exact resolve eq22029 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22029
  have eq22033 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq21327 eq22031
    | exact resolve eq22031 eq21327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22031
  have eq22035 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq26 eq22033
    | exact resolve eq22033 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22033
  have eq22050 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq21757 eq41
    | exact resolve eq41 eq21757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq21757
  have eq22069 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20 eq22050
    | exact resolve eq22050 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22050
  have eq22078 : (σ x) = (k (σ x) (σ y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq21327 eq22069
    | exact resolve eq22069 eq21327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22069
  have eq24776 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq22035 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | (have r₁ := eq28 (σ x) (σ y)
       have r₂ := eq22035
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq22035
       grind)
    | exact resolve eq28 eq22035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22035
  have eq24780 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) ∨ x = y := by grind
  clear eq24776
  have eq24789 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq26 eq24780
    | exact resolve eq24780 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24780
  have eq24792 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | (have r₁ := eq24789
       have r₂ := eq176
       grind)
    | exact resolve eq24789 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24789
  have eq24794 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq22078 eq24792
    | exact resolve eq24792 eq22078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22078 eq24792
  have eq24795 : y = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq24794
  have eq24806 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq24795 eq6634
    | (have j0 := eq6634 (M.op x y) y
       grind)
    | exact resolve eq6634 eq24795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6634
  have eq24807 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq24795 eq6386
    | (have j0 := eq6386 y (M.op x y)
       grind)
    | exact resolve eq6386 eq24795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6386
  have eq24814 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq24807
  have eq24815 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq24806
  have eq24823 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq24814
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24814
    | exact resolve eq24814 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24814
  have eq24824 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq24815
    | exact resolve eq24815 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24815
  have eq24830 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq24823
    | exact resolve eq24823 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24823
  have eq24831 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq24824
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24824
    | exact resolve eq24824 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24824
  have eq24837 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq24830
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24830
    | exact resolve eq24830 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24830
  have eq24838 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq24831
    | exact resolve eq24831 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24831
  have eq24841 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq24837
    | exact resolve eq24837 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24837
  have eq24842 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq24838
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24838
    | exact resolve eq24838 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24838
  have eq24844 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq24841
    | exact resolve eq24841 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24841
  have eq24845 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq24842
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24842
    | exact resolve eq24842 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24842
  have eq24847 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq24844
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24844
    | exact resolve eq24844 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24844
  have eq24848 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq24845
    | exact resolve eq24845 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24845
  have eq24850 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21327 eq24847
    | exact resolve eq24847 eq21327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24847
  have eq24851 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21327 eq24848
    | exact resolve eq24848 eq21327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24848
  have eq24853 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21327 eq24850
    | exact resolve eq24850 eq21327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24850
  have eq24854 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq24851
    | exact resolve eq24851 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24851
  have eq24855 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24854
  have eq24857 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq24853
    | exact resolve eq24853 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24853
  have eq24858 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21327 eq24855
    | exact resolve eq24855 eq21327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24855
  have eq24860 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21327 eq24857
    | exact resolve eq24857 eq21327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24857
  have eq24861 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21327 eq24858
    | exact resolve eq24858 eq21327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24858
  have eq24862 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24861
  have eq24864 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq24860
    | exact resolve eq24860 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24860
  have eq24865 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24864
  have eq24980 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24865 eq24862
    | exact resolve eq24862 eq24865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24862
  have eq24981 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24865 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | (have r₁ := eq28 (σ x) (σ y)
       have r₂ := eq24865
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq24865
       grind)
    | exact resolve eq28 eq24865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq24865
  have eq24985 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq24981
  have eq24986 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq24985
  have eq24987 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq24980
  have eq24995 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq24986
    | exact resolve eq24986 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24986
  have eq24996 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq24995
       have r₂ := eq176
       grind)
    | exact resolve eq24995 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq24995
  have eq24997 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq24987 eq24996
    | exact resolve eq24996 eq24987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24987 eq24996
  have eq25033 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq24997 eq91
    | exact resolve eq91 eq24997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq24997
  have eq25060 : y = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq32 eq25033
    | exact resolve eq25033 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25033
  have eq25065 : y = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21114 eq25060
    | exact resolve eq25060 eq21114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21114 eq25060
  have eq25084 : y ≠ y ∨ y = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq25065 eq981
    | (have j0 := eq981 y (M.op x y)
       grind)
    | (have r₁ := eq981 y (M.op x y)
       have r₂ := eq25065
       grind)
    | exact resolve eq981 eq25065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq25085 : y = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq25084
  have eq25094 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21287 eq25085
    | exact resolve eq25085 eq21287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25085
  have eq30376 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq25094 eq14
    | (have r₁ := eq14 y (M.op x y)
       have r₂ := eq25094
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq25094
       grind)
    | exact resolve eq14 eq25094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25094
  have eq30378 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq30376
  have eq30381 : y = (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq24795 eq30378
    | exact resolve eq30378 eq24795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24795 eq30378
  have eq30382 : y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq30381
  have eq30390 : y ≠ y ∨ y = (M.op (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq30382 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq30382
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq30382
       grind)
    | exact resolve eq13 eq30382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30382
  have eq30392 : y = (M.op (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq30390
  have eq30398 : y = (M.op (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq30392
       have r₂ := eq21467
       grind)
    | exact resolve eq30392 eq21467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30392
  have eq30399 : y = (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21287 eq30398
    | exact resolve eq30398 eq21287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21287 eq30398
  have eq30400 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq30399
       have r₂ := eq21467
       grind)
    | exact resolve eq30399 eq21467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21467 eq30399
  have eq30410 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq30400 eq25065
    | exact resolve eq25065 eq30400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25065 eq30400
  have eq30445 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq30410
  have eq30504 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30445 eq27
    | exact resolve eq27 eq30445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30445
  have eq30510 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq30504
       have r₂ := eq21327
       grind)
    | exact resolve eq30504 eq21327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21327 eq30504
  have eq30512 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30510 eq32
    | exact resolve eq32 eq30510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq30510
  have eq30698 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq30512
    | exact resolve eq30512 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq30512
  have eq30699 : y = (M.op x y) ∨ x = y := by grind
  clear eq30698
  have eq30785 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq30699
  have eq30795 : x = y := by
    first
    | (have r₁ := eq30785
       have r₂ := eq21239
       grind)
    | exact resolve eq30785 eq21239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21239 eq30785
  have eq30819 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq30795
       grind)
    | exact superpose eq30795 eq18
    | exact resolve eq18 eq30795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq30820 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq30795
       grind)
    | exact superpose eq30795 eq24
    | exact resolve eq24 eq30795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq30823 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq175
       have i₂ := eq30795
       grind)
    | exact superpose eq30795 eq175
    | exact resolve eq175 eq30795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq30795
  have eq30896 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq30820
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30820
    | exact resolve eq30820 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30820
  have eq30901 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq30896 eq26
    | exact resolve eq26 eq30896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq30896
  have eq31080 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq30819
       grind)
    | exact superpose eq30819 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq30819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30819
  have eq31084 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq31080
  have eq31088 : (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq31084
       have r₂ := eq30823
       grind)
    | exact resolve eq31084 eq30823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30823 eq31084
  have eq31097 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30901 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq30901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31100 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq30901 eq14
    | exact resolve eq14 eq30901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30901
  have eq31101 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31097
  have eq31109 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq31101
       have r₂ := eq31100
       grind)
    | exact resolve eq31101 eq31100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31100 eq31101
  have eq31125 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq31088
       grind)
    | exact superpose eq31088 eq40
    | exact resolve eq40 eq31088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq31088
  have eq31147 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq31125
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31125
    | exact resolve eq31125 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31125
  have eq31154 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31109 eq31147
    | exact resolve eq31147 eq31109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31109 eq31147
  have eq31161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq31154
    | exact resolve eq31154 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq31154
  have eq31166 : False := by grind
  exact eq31166

/-- `x □ y = if m(Y,X) = X then X else if m(X,Y) = X then Y else if m(X,Y) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyx_x_pxy_x_pxy_y_x_y_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
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
    | (have i₁ := eq16 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq16
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq44
    | exact resolve eq44 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq47
    | exact resolve eq47 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq59
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq72
    | exact resolve eq72 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : y ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq971 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq972 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq976 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq14
    | (have j0 := eq14 X1 X0
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq977 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq978 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq982 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq976 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq976 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq976 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq976 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq976 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq988 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq989 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq990 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq989 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq991 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq990 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq990 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq990 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq990 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq990 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq992 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq978 eq991
    | (have j0 := eq991 X0 X1
       have j1 := eq978 X0 X1
       grind)
    | (have r₁ := eq991 X1 X1
       have r₂ := eq978 X1 X1
       grind)
    | exact resolve eq991 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq993 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq992 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq2749 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq971
       grind)
    | exact superpose eq971 eq40
    | exact resolve eq40 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2750 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2749
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2749
    | exact resolve eq2749 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749
  have eq2752 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq2750
    | exact resolve eq2750 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2750
  have eq6753 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq977 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq977
    | (have j0 := eq977 (σ X0) (σ X1)
       grind)
    | exact resolve eq977 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10504 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq978 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq978
    | (have j0 := eq978 (σ X0) (σ X1)
       grind)
    | exact resolve eq978 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq15398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2752 eq972
    | exact resolve eq972 eq2752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15411 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq15398
       have r₂ := eq27
       grind)
    | exact resolve eq15398 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15398
  have eq15422 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq15411 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq15411
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq15411
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq15411
       grind)
    | exact resolve eq14 eq15411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15411
  have eq15423 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq15422
  have eq15439 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq15423 eq152
    | exact resolve eq152 eq15423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15423
  have eq15449 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq15439
    | exact resolve eq15439 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15439
  have eq15456 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq15449
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq15449
       have r₂ := eq14 y x
       grind)
    | (have r₁ := eq15449
       have r₂ := eq14 x y
       grind)
    | exact resolve eq15449 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15449
  have eq15465 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq971
       have i₂ := eq15456
       grind)
    | exact superpose eq15456 eq971
    | exact resolve eq971 eq15456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15467 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq15456
       grind)
    | exact superpose eq15456 eq40
    | exact resolve eq40 eq15456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15456
  have eq15472 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15465
  have eq15479 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15467
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15467
    | exact resolve eq15467 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15467
  have eq15488 : x ≠ x ∨ x = y ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq15472
       grind)
    | exact superpose eq15472 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15472
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15472
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15472
       grind)
    | exact resolve eq12 eq15472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15472
  have eq15492 : x = y ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15488
  have eq15495 : y = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15492
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15492
    | exact resolve eq15492 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15492
  have eq15496 : y = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15495
  have eq15498 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15496
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15496
    | exact resolve eq15496 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15496
  have eq15504 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15479 eq972
    | exact resolve eq972 eq15479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972 eq15479
  have eq15513 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15504
  have eq15530 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15513 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15513
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15513
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15513
       grind)
    | exact resolve eq12 eq15513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15534 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15530
  have eq15537 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15534
    | exact resolve eq15534 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15534
  have eq15538 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15537
  have eq15540 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15538
    | exact resolve eq15538 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15538
  have eq15554 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq15498
       grind)
    | exact superpose eq15498 eq39
    | exact resolve eq39 eq15498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15498
  have eq15558 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15554
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15554
    | exact resolve eq15554 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15554
  have eq15562 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15558
    | exact resolve eq15558 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15558
  have eq15564 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq993 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq993
    | (have j0 := eq993 (σ X0) (σ X1)
       grind)
    | exact resolve eq993 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq16056 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15562 eq15540
    | exact resolve eq15540 eq15562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15540 eq15562
  have eq16067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq16056
  have eq16074 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq16067
       have r₂ := eq27
       grind)
    | exact resolve eq16067 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16067
  have eq16080 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16074 eq175
    | (have r₁ := eq175
       have r₂ := eq16074
       grind)
    | exact resolve eq175 eq16074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16083 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq16080
  have eq16094 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16083 eq141
    | exact resolve eq141 eq16083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16083
  have eq16105 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq16094
    | exact resolve eq16094 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16094
  have eq16112 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq16105
       have r₂ := eq174
       grind)
    | exact resolve eq16105 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16105
  have eq16120 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq16112
       grind)
    | exact superpose eq16112 eq39
    | exact resolve eq39 eq16112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16130 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16120
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16120
    | exact resolve eq16120 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16120
  have eq16148 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16130 eq977
    | (have j0 := eq977 (σ y) (σ x)
       grind)
    | (have r₁ := eq977 (σ y) (σ x)
       have r₂ := eq16130
       grind)
    | exact resolve eq977 eq16130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16149 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq16148
  have eq16154 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq16149
    | exact resolve eq16149 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16149
  have eq16162 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15513 eq16154
    | exact resolve eq16154 eq15513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16154
  have eq16163 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16162
  have eq16582 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16163 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq16163
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq16163
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16163
       grind)
    | exact resolve eq13 eq16163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16585 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16582
  have eq16588 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16585
    | exact resolve eq16585 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16585
  have eq16589 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16588
  have eq16603 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16589 eq16130
    | exact resolve eq16130 eq16589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16589
  have eq16620 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq16603
  have eq16632 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq15513 eq16620
    | exact resolve eq16620 eq15513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16620
  have eq16633 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq16632
  have eq16647 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16633 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16633
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq16633
       grind)
    | exact resolve eq12 eq16633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16633
  have eq16651 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16647
  have eq16652 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16651
  have eq16654 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16652
    | exact resolve eq16652 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16652
  have eq16655 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16654
  have eq16657 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16655
    | exact resolve eq16655 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16655
  have eq16692 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16657 eq16130
    | exact resolve eq16130 eq16657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16130
  have eq16704 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq16692
  have eq16718 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16704 eq988
    | (have r₁ := eq988
       have r₂ := eq16704
       grind)
    | exact resolve eq988 eq16704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq16724 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq16718
  have eq16725 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq16724
  have eq18729 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16163 eq16725
    | exact resolve eq16725 eq16163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18733 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq16725 eq16163
    | exact resolve eq16163 eq16725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16163 eq16725
  have eq18743 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq18733
  have eq18746 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq18729
  have eq18753 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq18743
       have r₂ := eq177
       grind)
    | exact resolve eq18743 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18743
  have eq18757 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq18746
       have r₂ := eq177
       grind)
    | exact resolve eq18746 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq18746
  have eq18761 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq18753
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq18753
       have r₂ := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq18753 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18753
  have eq18792 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq18757 eq90
    | exact resolve eq90 eq18757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18829 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq31 eq18792
    | exact resolve eq18792 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18792
  have eq18847 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18761 eq90
    | exact resolve eq90 eq18761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq18761
  have eq18879 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq18847
    | exact resolve eq18847 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18847
  have eq18892 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq18829 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq18829
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq18829
       grind)
    | exact resolve eq12 eq18829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18896 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq18892
  have eq18897 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by grind
  clear eq18896
  have eq18901 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq18897
    | exact resolve eq18897 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18897
  have eq18902 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ y = (k x y) := by grind
  clear eq18901
  have eq18905 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq18902
    | exact resolve eq18902 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18902
  have eq18906 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (k x y) := by
    first
    | exact superpose eq16704 eq18905
    | exact resolve eq18905 eq16704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16704 eq18905
  have eq18919 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18879 eq152
    | exact resolve eq152 eq18879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq18879
  have eq18938 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq18919
    | exact resolve eq18919 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18919
  have eq18999 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18938
       have i₂ := eq971
       grind)
    | exact superpose eq971 eq18938
    | exact resolve eq18938 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19004 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq971
       have i₂ := eq18938
       grind)
    | exact superpose eq18938 eq971
    | exact resolve eq971 eq18938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19005 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq18938
       grind)
    | exact superpose eq18938 eq35
    | exact resolve eq35 eq18938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq19009 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq982 x y
       have i₂ := eq18938
       grind)
    | exact superpose eq18938 eq982
    | (have j0 := eq982 x y
       grind)
    | (have r₁ := eq982 x y
       have r₂ := eq18938
       grind)
    | exact resolve eq982 eq18938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982 eq18938
  have eq19021 : y = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq19009
  have eq19023 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19004
  have eq19026 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq18999
  have eq19033 : y = (k y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq19021
       have r₂ := eq14 x y
       grind)
    | (have r₁ := eq19021
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq19021 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19021
  have eq19036 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19005
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19005
    | exact resolve eq19005 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19005
  have eq19037 : x = (k x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq19023
       have r₂ := eq14 y x
       grind)
    | (have r₁ := eq19023
       have r₂ := eq14 x y
       grind)
    | (have r₁ := eq19023
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq19023 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19023
  have eq19046 : x = (M.op x y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19033
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19033
    | exact resolve eq19033 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19033
  have eq19047 : x = (M.op x y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19046
  have eq19054 : x = (M.op x y) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16112 eq19047
    | exact resolve eq19047 eq16112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16112 eq19047
  have eq19055 : y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq19054
  have eq19070 : y ≠ y ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq977 y x
       have i₂ := eq19055
       grind)
    | exact superpose eq19055 eq977
    | (have j0 := eq977 y x
       grind)
    | (have r₁ := eq977 y x
       have r₂ := eq19055
       grind)
    | (have r₁ := eq977 x y
       have r₂ := eq19055
       grind)
    | exact resolve eq977 eq19055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19073 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq6753 y x
       have i₂ := eq19055
       grind)
    | exact superpose eq19055 eq6753
    | (have j0 := eq6753 y x
       grind)
    | exact resolve eq6753 eq19055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19055
  have eq19076 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq19073
  have eq19078 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq19070
  have eq19085 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq19076
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19076
    | exact resolve eq19076 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19076
  have eq19086 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq19078
       have r₂ := eq14 x y
       grind)
    | (have r₁ := eq19078
       have r₂ := eq14 y x
       grind)
    | exact resolve eq19078 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19078
  have eq19093 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq19085
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19085
    | exact resolve eq19085 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19085
  have eq19094 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq19086
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19086
    | exact resolve eq19086 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19086
  have eq19096 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq19093
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19093
    | exact resolve eq19093 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19093
  have eq19097 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq19096
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19096
    | exact resolve eq19096 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19096
  have eq19098 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq19097
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19097
    | exact resolve eq19097 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19097
  have eq19099 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq19098
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19098
    | exact resolve eq19098 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19098
  have eq19100 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq26 eq19099
    | exact resolve eq19099 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19099
  have eq19101 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq18829 eq19100
    | exact resolve eq19100 eq18829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18829 eq19100
  have eq19102 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq19101
  have eq19146 : x ≠ x ∨ x = y ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19026
       grind)
    | exact superpose eq19026 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq19026
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq19026
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq19026
       grind)
    | exact resolve eq12 eq19026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19026
  have eq19150 : x ≠ x ∨ x = y ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq19146
  have eq19151 : x = y ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq19150
  have eq19152 : y = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19151
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19151
    | exact resolve eq19151 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19151
  have eq19153 : y = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq19152
  have eq19155 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19153
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19153
    | exact resolve eq19153 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19153
  have eq19162 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq19037
       grind)
    | exact superpose eq19037 eq40
    | exact resolve eq40 eq19037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq19037
  have eq19177 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19162
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19162
    | exact resolve eq19162 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19162
  have eq19251 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19177 eq18757
    | exact resolve eq18757 eq19177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18757 eq19177
  have eq19262 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq19251
  have eq19356 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19262 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq19262
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq19262
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq19262
       grind)
    | exact resolve eq12 eq19262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19262
  have eq19360 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19356
  have eq19361 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19360
  have eq19365 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq19361
    | exact resolve eq19361 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19361
  have eq19366 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq19365
  have eq19369 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq19366
    | exact resolve eq19366 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19366
  have eq19370 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq16074 eq19369
    | exact resolve eq19369 eq16074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16074 eq19369
  have eq19390 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq19370 eq107
    | exact resolve eq107 eq19370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq19370
  have eq19427 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq19390
    | exact resolve eq19390 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19390
  have eq19432 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq19155 eq19427
    | exact resolve eq19427 eq19155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19155 eq19427
  have eq19433 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq19432
  have eq19441 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq19433 eq175
    | (have r₁ := eq175
       have r₂ := eq19433
       grind)
    | exact resolve eq175 eq19433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19446 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq19441
  have eq19465 : (τ (σ y)) = (k (τ (σ y)) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq19446 eq141
    | exact resolve eq141 eq19446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19446
  have eq19489 : y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq19465
    | exact resolve eq19465 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19465
  have eq19498 : y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq19489
       have r₂ := eq174
       grind)
    | exact resolve eq19489 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19489
  have eq19510 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq19498
       grind)
    | exact superpose eq19498 eq39
    | exact resolve eq39 eq19498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq19529 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19510
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19510
    | exact resolve eq19510 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19510
  have eq19556 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19529 eq18906
    | exact resolve eq18906 eq19529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18906
  have eq19571 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ y = (k x y) := by grind
  clear eq19556
  have eq19587 : (M.op x y) = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19433 eq19571
    | exact resolve eq19571 eq19433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19571
  have eq20097 : y ≠ y ∨ y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19094
       grind)
    | exact superpose eq19094 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19094
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19094
       grind)
    | exact resolve eq13 eq19094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19094
  have eq20100 : y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq20097
  have eq20107 : y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq20100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20100
    | exact resolve eq20100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20100
  have eq20108 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq20107
  have eq20117 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19102 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19102
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19102
       grind)
    | exact resolve eq13 eq19102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19102
  have eq20120 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20117
  have eq20128 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq20120
    | exact resolve eq20120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20120
  have eq20129 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20128
  have eq20130 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19529 eq20129
    | exact resolve eq20129 eq19529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19529 eq20129
  have eq20131 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq20130
  have eq20139 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20131 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq20131
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq20131
       grind)
    | exact resolve eq14 eq20131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20131
  have eq20140 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq20139
  have eq20165 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20140 eq19036
    | exact resolve eq19036 eq20140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19036 eq20140
  have eq20176 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq20165
  have eq20191 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19433 eq20176
    | exact resolve eq20176 eq19433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19433 eq20176
  have eq20199 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19587 eq20191
    | exact resolve eq20191 eq19587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19587 eq20191
  have eq20200 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq20199
  have eq20209 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20200 eq27
    | exact resolve eq27 eq20200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20200
  have eq20800 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq19498
       have i₂ := eq20108
       grind)
    | exact superpose eq20108 eq19498
    | exact resolve eq19498 eq20108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20108
  have eq20819 : x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq20800
  have eq20842 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq971
       have i₂ := eq20819
       grind)
    | exact superpose eq20819 eq971
    | exact resolve eq971 eq20819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971 eq20819
  have eq20855 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20842
  have eq20879 : x ≠ x ∨ x = y ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq20855
       grind)
    | exact superpose eq20855 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq20855
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq20855
       grind)
    | exact resolve eq12 eq20855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20855
  have eq20883 : x ≠ x ∨ x = y ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq20879
  have eq20884 : x = y ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq20883
  have eq20887 : y = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20884
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20884
    | exact resolve eq20884 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20884
  have eq20888 : y = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq20887
  have eq20890 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20888
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20888
    | exact resolve eq20888 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20888
  have eq20949 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19498
       have i₂ := eq20890
       grind)
    | exact superpose eq20890 eq19498
    | exact resolve eq19498 eq20890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19498 eq20890
  have eq20963 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq20949
  have eq20979 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20963 eq31
    | exact resolve eq31 eq20963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20963
  have eq21093 : x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq20979
    | exact resolve eq20979 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20979
  have eq21094 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq21093
  have eq21096 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq21094
       grind)
    | exact superpose eq21094 eq24
    | exact resolve eq24 eq21094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21094
  have eq21149 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq21096
    | exact resolve eq21096 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21096
  have eq21206 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21149 eq20209
    | (have r₁ := eq20209
       have r₂ := eq21149
       grind)
    | exact resolve eq20209 eq21149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20209 eq21149
  have eq21207 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq21206
  have eq21208 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq21207
  have eq21266 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21208 eq31
    | exact resolve eq31 eq21208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21380 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq21266
    | exact resolve eq21266 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21266
  have eq21381 : x = (M.op x y) ∨ x = y := by grind
  clear eq21380
  have eq21428 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq21381
       grind)
    | exact superpose eq21381 eq18
    | exact resolve eq18 eq21381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21429 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq21381
       grind)
    | exact superpose eq21381 eq22
    | exact resolve eq22 eq21381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21432 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq176
       have i₂ := eq21381
       grind)
    | exact superpose eq21381 eq176
    | (have r₁ := eq176
       have r₂ := eq21381
       grind)
    | exact resolve eq176 eq21381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq21448 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (k (M.op x y) y) ∨ x = y := by grind
  clear eq21432
  have eq21466 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq21429
    | exact resolve eq21429 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21429
  have eq22088 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) ∨ (k y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq21448 eq12
    | (have j0 := eq12 y (M.op x y)
       grind)
    | (have r₁ := eq12 y (M.op x y)
       have r₂ := eq21448
       grind)
    | exact resolve eq12 eq21448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22090 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq21448 eq14
    | (have j0 := eq14 (M.op x y) y
       grind)
    | (have r₁ := eq14 (M.op x y) y
       have r₂ := eq21448
       grind)
    | exact resolve eq14 eq21448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21448
  have eq22091 : (M.op x y) = (k (M.op x y) y) ∨ y = (k (M.op x y) y) ∨ x = y := by grind
  clear eq22090
  have eq22092 : y = (M.op x y) ∨ y = (M.op (M.op x y) y) ∨ (k y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (k (M.op x y) y) ∨ x = y := by grind
  clear eq22088
  have eq22095 : y = (M.op x y) ∨ y = (M.op x y) ∨ (k y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq21428 eq22092
    | exact resolve eq22092 eq21428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22092
  have eq22096 : y = (M.op x y) ∨ (k y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (k (M.op x y) y) ∨ x = y := by grind
  clear eq22095
  have eq22099 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq21428 eq22096
    | exact resolve eq22096 eq21428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22096
  have eq22108 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq22091 eq6753
    | (have j0 := eq6753 (M.op x y) y
       grind)
    | exact resolve eq6753 eq22091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6753
  have eq22111 : y ≠ (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = y := by grind
  clear eq22091
  have eq22112 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ x = y := by grind
  clear eq22108
  have eq22117 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq22112
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22112
    | exact resolve eq22112 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22112
  have eq22124 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq20 eq22117
    | exact resolve eq22117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22117
  have eq22131 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq22124
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22124
    | exact resolve eq22124 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22124
  have eq22137 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq20 eq22131
    | exact resolve eq22131 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22131
  have eq22140 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq20 eq22137
    | exact resolve eq22137 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22137
  have eq22143 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq22140
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22140
    | exact resolve eq22140 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22140
  have eq22146 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq21466 eq22143
    | exact resolve eq22143 eq21466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22143
  have eq22149 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq21466 eq22146
    | exact resolve eq22146 eq21466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22146
  have eq22152 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq26 eq22149
    | exact resolve eq22149 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22149
  have eq22155 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq21466 eq22152
    | exact resolve eq22152 eq21466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22152
  have eq22158 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq26 eq22155
    | exact resolve eq22155 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22155
  have eq24885 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq22099 eq36
    | exact resolve eq36 eq22099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq22099
  have eq24911 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | (have r₁ := eq24885
       have r₂ := eq22111
       grind)
    | exact resolve eq24885 eq22111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24885
  have eq24919 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq20 eq24911
    | exact resolve eq24911 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24911
  have eq24927 : (σ x) = (k (σ y) (σ x)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq21466 eq24919
    | exact resolve eq24919 eq21466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24919
  have eq26545 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq22158 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq22158
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq22158
       grind)
    | exact resolve eq12 eq22158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22158
  have eq26549 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by grind
  clear eq26545
  have eq26557 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq26 eq26549
    | exact resolve eq26549 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26549
  have eq26558 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by grind
  clear eq26557
  have eq26563 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq26 eq26558
    | exact resolve eq26558 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26558
  have eq26564 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16657 eq26563
    | exact resolve eq26563 eq16657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16657 eq26563
  have eq29741 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26564 eq24927
    | exact resolve eq24927 eq26564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26564
  have eq29753 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq29741
  have eq29783 : y = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq29753
       have r₂ := eq22111
       grind)
    | exact resolve eq29753 eq22111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22111 eq29753
  have eq29814 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29783 eq15564
    | (have j0 := eq15564 (M.op x y) y
       grind)
    | exact resolve eq15564 eq29783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15564 eq29783
  have eq29815 : (σ y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq29814
  have eq29839 : (σ y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq29815
    | exact resolve eq29815 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29815
  have eq29847 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29839
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29839
    | exact resolve eq29839 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29839
  have eq29855 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29847
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29847
    | exact resolve eq29847 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29847
  have eq29860 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq29855
    | exact resolve eq29855 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29855
  have eq29864 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29860
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29860
    | exact resolve eq29860 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29860
  have eq29868 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq29864
    | exact resolve eq29864 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29864
  have eq29872 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21466 eq29868
    | exact resolve eq29868 eq21466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29868
  have eq29876 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq29872
    | exact resolve eq29872 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29872
  have eq29877 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq29876
  have eq29881 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21466 eq29877
    | exact resolve eq29877 eq21466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29877
  have eq29883 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq29881
    | exact resolve eq29881 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29881
  have eq29884 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq29883
  have eq29886 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21466 eq29884
    | exact resolve eq29884 eq21466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29884
  have eq29887 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq29886
  have eq29889 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29887 eq175
    | (have r₁ := eq175
       have r₂ := eq29887
       grind)
    | exact resolve eq175 eq29887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29887
  have eq29895 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq29889
  have eq29918 : (σ x) = (σ y) ∨ y = (k (M.op x y) y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29895 eq24927
    | exact resolve eq24927 eq29895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24927
  have eq29921 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29895 eq141
    | exact resolve eq141 eq29895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29895
  have eq29931 : y = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29918
  have eq29951 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31 eq29921
    | exact resolve eq29921 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29921
  have eq29958 : y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21208 eq29951
    | exact resolve eq29951 eq21208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21208 eq29951
  have eq30089 : y ≠ y ∨ y = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29958 eq977
    | (have j0 := eq977 y (M.op x y)
       grind)
    | (have r₁ := eq977 y (M.op x y)
       have r₂ := eq29958
       grind)
    | exact resolve eq977 eq29958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq30096 : y = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30089
  have eq30121 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21428 eq30096
    | exact resolve eq30096 eq21428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30096
  have eq30373 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30121 eq14
    | (have j0 := eq14 (M.op x y) y
       grind)
    | (have r₁ := eq14 (M.op x y) y
       have r₂ := eq30121
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq30121
       grind)
    | exact resolve eq14 eq30121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30121
  have eq30375 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30373
  have eq30378 : y = (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29931 eq30375
    | exact resolve eq30375 eq29931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29931 eq30375
  have eq30379 : y = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30378
  have eq30388 : y ≠ y ∨ y = (M.op (M.op x y) y) ∨ (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30379 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq30379
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq30379
       grind)
    | exact resolve eq13 eq30379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30379
  have eq30390 : y = (M.op (M.op x y) y) ∨ (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30388
  have eq30394 : y = (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21428 eq30390
    | exact resolve eq30390 eq21428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21428 eq30390
  have eq30395 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30394
  have eq30405 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30395 eq29958
    | exact resolve eq29958 eq30395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29958 eq30395
  have eq30441 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30405
  have eq30460 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30441 eq27
    | exact resolve eq27 eq30441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30441
  have eq30476 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq30460
       have r₂ := eq21466
       grind)
    | exact resolve eq30460 eq21466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21466 eq30460
  have eq30478 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30476 eq31
    | exact resolve eq31 eq30476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq30476
  have eq30622 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq30478
    | exact resolve eq30478 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30478
  have eq30623 : y = (M.op x y) ∨ x = y := by grind
  clear eq30622
  have eq30709 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq30623
  have eq30721 : x = y := by
    first
    | (have r₁ := eq30709
       have r₂ := eq21381
       grind)
    | exact resolve eq30709 eq21381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21381 eq30709
  have eq30745 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq30721
       grind)
    | exact superpose eq30721 eq18
    | exact resolve eq18 eq30721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq30746 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq30721
       grind)
    | exact superpose eq30721 eq24
    | exact resolve eq24 eq30721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq30749 : x ≠ (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq174
       have i₂ := eq30721
       grind)
    | exact superpose eq30721 eq174
    | exact resolve eq174 eq30721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq30798 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq30746
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30746
    | exact resolve eq30746 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30746
  have eq30799 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq30798 eq26
    | exact resolve eq26 eq30798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq30847 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30798 eq2752
    | exact resolve eq2752 eq30798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752
  have eq30855 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30798 eq15513
    | exact resolve eq15513 eq30798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15513
  have eq30875 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq30855
  have eq30883 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30875
       have i₂ := eq30721
       grind)
    | exact superpose eq30721 eq30875
    | exact resolve eq30875 eq30721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30875
  have eq30884 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30883
  have eq30895 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq30847
       have i₂ := eq30721
       grind)
    | exact superpose eq30721 eq30847
    | exact resolve eq30847 eq30721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30847
  have eq30896 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq30895
  have eq30943 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30799 eq30884
    | exact resolve eq30884 eq30799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30884
  have eq30944 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq30943
  have eq30947 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq30896
       have i₂ := eq30721
       grind)
    | exact superpose eq30721 eq30896
    | exact resolve eq30896 eq30721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30721 eq30896
  have eq30948 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq30947
       have i₂ := eq30745
       grind)
    | exact superpose eq30745 eq30947
    | exact resolve eq30947 eq30745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30745 eq30947
  have eq30949 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq30948
  have eq30979 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30944 eq27
    | exact resolve eq27 eq30944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30980 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30944 eq175
    | exact resolve eq175 eq30944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq30944
  have eq30996 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30980
       have r₂ := eq30798
       grind)
    | exact resolve eq30980 eq30798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30980
  have eq30998 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30798 eq30996
    | exact resolve eq30996 eq30798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30798 eq30996
  have eq31780 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30998 eq30949
    | exact resolve eq30949 eq30998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30949
  have eq31783 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30998 eq141
    | exact resolve eq141 eq30998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq30998
  have eq31803 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq31780
  have eq31820 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq31783
    | exact resolve eq31783 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq31783
  have eq31822 : x = (M.op x y) := by
    first
    | (have r₁ := eq31803
       have r₂ := eq30979
       grind)
    | exact resolve eq31803 eq30979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30979 eq31803
  have eq31829 : x = (k x x) := by
    first
    | (have r₁ := eq31820
       have r₂ := eq30749
       grind)
    | exact resolve eq31820 eq30749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30749 eq31820
  have eq31832 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq31829
       have i₂ := eq31822
       grind)
    | exact superpose eq31822 eq31829
    | exact resolve eq31829 eq31822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31829
  have eq31836 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq31822
       grind)
    | exact superpose eq31822 eq22
    | exact resolve eq22 eq31822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31822
  have eq31899 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq31836 eq20
    | exact resolve eq20 eq31836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31836
  have eq32826 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq31832 eq10504
    | (have j0 := eq10504 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq10504 eq31832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10504 eq31832
  have eq32827 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq32826
  have eq32828 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq32827
  have eq32838 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq32828
    | exact resolve eq32828 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq32828
  have eq32846 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31899 eq32838
    | exact resolve eq32838 eq31899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32838
  have eq32866 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32846 eq30799
    | exact resolve eq30799 eq32846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30799 eq32846
  have eq32878 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq32866 eq27
    | exact resolve eq27 eq32866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32866
  have eq32898 : False := by grind
  exact eq32898

/-- `x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = Y then m(Y,X) else if m(X,Y) = X then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyx_x_pxy_y_pxy_x_pyx_pyx_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq72 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq92 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq97
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq117 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq132 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq146 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq186 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq16
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq249 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq16
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq272 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq339 : (k x (k x x)) = (τ (k (σ x) (k (σ x) (σ x)))) := by
    first
    | exact superpose eq49 eq226
    | exact resolve eq226 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq272 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq272
    | exact resolve eq272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq609 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq91 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq91 X0 X0
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq616 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq609 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq619 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq616 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq616 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq616 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq616 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq616 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq629 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq619 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq619
    | (have j0 := eq619 X0 X1
       grind)
    | exact resolve eq619 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq630 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq629 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq3511 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq92 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq92
    | (have j0 := eq92 x
       grind)
    | exact resolve eq92 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3515 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (k (σ x) (σ X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq92 eq56
    | (have j0 := eq56 (σ x) (σ X0)
       have j1 := eq92 X0
       grind)
    | (have r₁ := eq56 (σ x) (σ X0)
       have r₂ := eq92 X0
       grind)
    | (have r₁ := eq56 (σ x) (σ x)
       have r₂ := eq92 x
       grind)
    | (have r₁ := eq56 (σ X0) (σ x)
       have r₂ := eq92 X0
       grind)
    | exact resolve eq56 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3517 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq92 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq3520 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3511
  have eq3522 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (k (σ x) (σ X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3515 X0
       have j1 := eq14 (σ x) (σ X0)
       grind)
    | (have r₁ := eq3515 X0
       have r₂ := eq14 (σ X0) (σ x)
       grind)
    | (have r₁ := eq3515 x
       have r₂ := eq14 (σ x) (σ x)
       grind)
    | (have r₁ := eq3515 X0
       have r₂ := eq14 (σ x) (σ X0)
       grind)
    | exact resolve eq3515 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3515
  have eq3526 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3520
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3520
    | exact resolve eq3520 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq3520
  have eq3542 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (k (σ x) (σ X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3522 X0
       have j1 := eq56 (σ x) (σ X0)
       grind)
    | (have r₁ := eq3522 X0
       have r₂ := eq56 (σ x) (σ X0)
       grind)
    | (have r₁ := eq3522 x
       have r₂ := eq56 (σ x) (σ x)
       grind)
    | exact resolve eq3522 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522
  have eq3545 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | (have r₁ := eq3526
       have r₂ := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq3526 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526
  have eq3549 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq3542
    | (have j0 := eq3542 X0
       grind)
    | exact resolve eq3542 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3542
  have eq3551 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3545 eq49
    | exact resolve eq49 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3670 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq93 eq56
    | (have j0 := eq56 (σ y) (σ X0)
       have j1 := eq93 X0
       grind)
    | (have r₁ := eq56 (σ y) (σ X0)
       have r₂ := eq93 X0
       grind)
    | (have r₁ := eq56 (σ y) (σ y)
       have r₂ := eq93 y
       grind)
    | (have r₁ := eq56 (σ X0) (σ y)
       have r₂ := eq93 X0
       grind)
    | exact resolve eq56 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq3677 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3670 X0
       have j1 := eq14 (σ y) (σ X0)
       grind)
    | (have r₁ := eq3670 X0
       have r₂ := eq14 (σ X0) (σ y)
       grind)
    | (have r₁ := eq3670 y
       have r₂ := eq14 (σ y) (σ y)
       grind)
    | (have r₁ := eq3670 X0
       have r₂ := eq14 (σ y) (σ X0)
       grind)
    | exact resolve eq3670 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3670
  have eq3703 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3677 X0
       have j1 := eq56 (σ y) (σ X0)
       grind)
    | (have r₁ := eq3677 X0
       have r₂ := eq56 (σ y) (σ X0)
       grind)
    | (have r₁ := eq3677 y
       have r₂ := eq56 (σ y) (σ y)
       grind)
    | exact resolve eq3677 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3677
  have eq3717 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq3703
    | (have j0 := eq3703 X0
       grind)
    | exact resolve eq3703 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3703
  have eq3852 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq134
    | (have j0 := eq134 (M.op x y)
       grind)
    | exact resolve eq134 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq3859 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3852
  have eq3863 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq133 eq3859
    | exact resolve eq3859 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq3859
  have eq3896 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq14 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq3863
       have r₂ := eq14 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3863 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3863
  have eq4066 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (k (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq146 eq12
    | (have j0 := eq12 (σ X0) (σ x)
       have j1 := eq146 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq146 x
       grind)
    | (have r₁ := eq12 (σ X0) (σ x)
       have r₂ := eq146 X0
       grind)
    | exact resolve eq12 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq4071 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (k (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq4066 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4066
  have eq4075 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (k (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq4071 X0
       have j1 := eq12 (σ X0) (σ x)
       grind)
    | (have r₁ := eq4071 x
       have r₂ := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq4071 X0
       have r₂ := eq12 (σ X0) (σ x)
       grind)
    | exact resolve eq4071 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4071
  have eq4113 : ∀ X0 : G, (σ x) = (σ (k X0 x)) ∨ (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq39 eq4075
    | (have j0 := eq4075 X0
       grind)
    | exact resolve eq4075 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4075
  have eq4114 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq4113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4113
  have eq4273 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ y) = (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (k (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq186 eq12
    | (have j0 := eq12 (σ X0) (σ y)
       have j1 := eq186 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ y)
       have r₂ := eq186 y
       grind)
    | (have r₁ := eq12 (σ X0) (σ y)
       have r₂ := eq186 X0
       grind)
    | exact resolve eq12 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4277 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq186 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq4278 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ y) = (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (k (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq4273 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4273
  have eq4282 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ y) = (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (k (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq4278 X0
       have j1 := eq12 (σ X0) (σ y)
       grind)
    | (have r₁ := eq4278 y
       have r₂ := eq12 (σ y) (σ y)
       grind)
    | (have r₁ := eq4278 X0
       have r₂ := eq12 (σ X0) (σ y)
       grind)
    | exact resolve eq4278 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278
  have eq4320 : ∀ X0 : G, (σ y) = (σ (k X0 y)) ∨ (σ X0) ≠ (σ (k X0 y)) ∨ (σ y) = (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq40 eq4282
    | (have j0 := eq4282 X0
       grind)
    | exact resolve eq4282 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4282
  have eq4321 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ y) = (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq4320 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4320
  have eq4396 : (k x (k x x)) = (τ (k (σ x) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq3545 eq339
    | exact resolve eq339 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq5293 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq630 (τ X1) (τ X0)
       have i₂ := eq395 X0 X1
       grind)
    | exact superpose eq395 eq630
    | (have j0 := eq630 (τ X0) (τ X1)
       grind)
    | exact resolve eq630 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq630
  have eq5471 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5293 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq5293
    | (have j0 := eq5293 X0 X1
       grind)
    | exact resolve eq5293 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5293
  have eq5555 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5471 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5471
    | (have j0 := eq5471 X0 X1
       grind)
    | exact resolve eq5471 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5471
  have eq5639 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ X1)) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5555 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq5555
    | (have j0 := eq5555 X0 X1
       grind)
    | exact resolve eq5555 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5555
  have eq5721 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5639 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5639
    | (have j0 := eq5639 X0 X1
       grind)
    | exact resolve eq5639 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5639
  have eq5803 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5721 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5721
    | (have j0 := eq5721 X0 X1
       grind)
    | exact resolve eq5721 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5721
  have eq5885 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5803 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5803
    | (have j0 := eq5803 X0 X1
       grind)
    | exact resolve eq5803 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5803
  have eq5912 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5885 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5885
    | (have j0 := eq5885 X0 X1
       grind)
    | exact resolve eq5885 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5885
  have eq5937 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5912 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5912
    | (have j0 := eq5912 X0 X1
       grind)
    | exact resolve eq5912 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5912
  have eq10807 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3545 eq109
    | exact resolve eq109 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq14181 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq10807
       grind)
    | exact superpose eq10807 eq16
    | exact resolve eq16 eq10807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10807
  have eq14232 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3551 eq14181
    | exact resolve eq14181 eq3551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14181
  have eq14235 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq14 x x
       grind)
    | (have r₁ := eq14232
       have r₂ := eq14 x x
       grind)
    | exact resolve eq14232 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14232
  have eq22044 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22045 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq22044
    | exact resolve eq22044 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22044
  have eq22056 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq22045
       have r₂ := eq27
       grind)
    | exact resolve eq22045 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22045
  have eq22060 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq22056
    | exact resolve eq22056 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22056
  have eq22062 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq22060
    | exact resolve eq22060 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22060
  have eq22065 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22062 eq14
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq22062
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq22062
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq22062
       grind)
    | exact resolve eq14 eq22062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22062
  have eq22066 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq22065
  have eq22149 : (τ (σ x)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22066 eq55
    | exact resolve eq55 eq22066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22066
  have eq22178 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq22149
    | exact resolve eq22149 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22149
  have eq43114 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq22178
       grind)
    | exact superpose eq22178 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq22178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22178
  have eq43115 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq43114
  have eq43119 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq43115
    | exact resolve eq43115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43115
  have eq43120 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq43119
  have eq43136 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq43120
    | exact resolve eq43120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43120
  have eq43137 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43136
  have eq43168 : x ≠ x ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq43137
       grind)
    | exact superpose eq43137 eq56
    | (have j0 := eq56 y x
       grind)
    | (have r₁ := eq56 y x
       have r₂ := eq43137
       grind)
    | (have r₁ := eq56 x y
       have r₂ := eq43137
       grind)
    | (have r₁ := eq56 (σ x) (σ y)
       have r₂ := eq43137
       grind)
    | exact resolve eq56 eq43137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43169 : x ≠ x ∨ x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq43137
       grind)
    | exact superpose eq43137 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq43137
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq43137
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq43137
       grind)
    | exact resolve eq14 eq43137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43137
  have eq43170 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43169
  have eq43171 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43168
  have eq43172 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43171
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq43171
    | exact resolve eq43171 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43171
  have eq43173 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq43172
       have r₂ := eq50
       grind)
    | exact resolve eq43172 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43172
  have eq43178 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq43173
       grind)
    | exact superpose eq43173 eq70
    | exact resolve eq70 eq43173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43173
  have eq43230 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq43178
    | exact resolve eq43178 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43178
  have eq43689 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq613 x y
       have i₂ := eq43170
       grind)
    | exact superpose eq43170 eq613
    | (have j0 := eq613 x y
       grind)
    | exact resolve eq613 eq43170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq43170
  have eq43696 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43689
  have eq43701 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43696
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43696
    | exact resolve eq43696 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43696
  have eq43714 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43701
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43701
    | exact resolve eq43701 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43701
  have eq43720 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq43714
    | exact resolve eq43714 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43714
  have eq43721 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43720
  have eq43725 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43721
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43721
    | exact resolve eq43721 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43721
  have eq43730 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43725
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43725
    | exact resolve eq43725 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43725
  have eq43734 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq43730
    | exact resolve eq43730 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43730
  have eq43735 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq43734
  have eq43741 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43735
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43735
    | exact resolve eq43735 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43735
  have eq43744 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43741
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43741
    | exact resolve eq43741 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43741
  have eq44136 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43744 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | (have r₁ := eq56 (σ y) (σ x)
       have r₂ := eq43744
       grind)
    | (have r₁ := eq56 (σ x) (σ y)
       have r₂ := eq43744
       grind)
    | (have r₁ := eq56 x y
       have r₂ := eq43744
       grind)
    | exact resolve eq56 eq43744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43744
  have eq44139 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq44136
  have eq44141 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq44139
    | exact resolve eq44139 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44139
  have eq44142 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq44141
       have r₂ := eq51
       grind)
    | exact resolve eq44141 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44141
  have eq44502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44142 eq43230
    | exact resolve eq43230 eq44142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43230 eq44142
  have eq44509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq44502
  have eq44528 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq44509
       have r₂ := eq27
       grind)
    | exact resolve eq44509 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44509
  have eq44532 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44528 eq51
    | (have r₁ := eq51
       have r₂ := eq44528
       grind)
    | exact resolve eq51 eq44528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44528
  have eq44582 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq44532
  have eq44939 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44582 eq77
    | exact resolve eq77 eq44582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq44582
  have eq45011 : y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq44939
    | exact resolve eq44939 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44939
  have eq45382 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq45011
       grind)
    | exact superpose eq45011 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq45011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45383 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq45382
  have eq45404 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45383
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq45383
    | exact resolve eq45383 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45383
  have eq45405 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq45404
  have eq65637 : y ≠ y ∨ x = y ∨ y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq45405
       grind)
    | exact superpose eq45405 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq45405
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq45405
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq45405
       grind)
    | exact resolve eq12 eq45405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65640 : x ≠ y ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq45405
  have eq65641 : x = y ∨ y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq65637
  have eq65646 : y = (M.op x y) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65641
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq65641
    | exact resolve eq65641 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65641
  have eq65647 : y = (M.op x y) ∨ x = y ∨ x = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq65646
  have eq638254 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq65647
       have r₂ := eq65640
       grind)
    | exact resolve eq65647 eq65640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65647
  have eq638314 : x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45011
       have i₂ := eq638254
       grind)
    | exact superpose eq638254 eq45011
    | exact resolve eq45011 eq638254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638254
  have eq638643 : x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq638314
  have eq638711 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq638643
       have r₂ := eq65640
       grind)
    | exact resolve eq638643 eq65640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65640 eq638643
  have eq639671 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq638711
       grind)
    | exact superpose eq638711 eq56
    | (have j0 := eq56 y x
       grind)
    | (have r₁ := eq56 y x
       have r₂ := eq638711
       grind)
    | (have r₁ := eq56 x y
       have r₂ := eq638711
       grind)
    | exact resolve eq56 eq638711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638711
  have eq639672 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq639671
  have eq639675 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq639672
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq639672
    | exact resolve eq639672 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639672
  have eq639676 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq639675
       have r₂ := eq50
       grind)
    | exact resolve eq639675 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639675
  have eq639723 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45011
       have i₂ := eq639676
       grind)
    | exact superpose eq639676 eq45011
    | exact resolve eq45011 eq639676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45011 eq639676
  have eq639943 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq639723
  have eq640156 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq639943 eq27
    | exact resolve eq27 eq639943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640157 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq639943 eq51
    | exact resolve eq51 eq639943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640159 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq639943 eq79
    | (have r₁ := eq79
       have r₂ := eq639943
       grind)
    | exact resolve eq79 eq639943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq639943
  have eq640160 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq640159
  have eq686816 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq640160 eq55
    | exact resolve eq55 eq640160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq686912 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq686816
    | exact resolve eq686816 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686816
  have eq696927 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq686912 eq14
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq686912
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq686912
       grind)
    | exact resolve eq14 eq686912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686912
  have eq696930 : (σ x) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq696927
  have eq714786 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq696930 eq118
    | exact resolve eq118 eq696930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696930
  have eq714858 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq714786
  have eq714870 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq714858
       have r₂ := eq640156
       grind)
    | exact resolve eq714858 eq640156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640156 eq714858
  have eq714877 : y = (k x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq714870
       have r₂ := eq78
       grind)
    | exact resolve eq714870 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714870
  have eq714917 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq714877
       grind)
    | exact superpose eq714877 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq714877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714877
  have eq714930 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq714917
  have eq714953 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq714930
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq714930
    | exact resolve eq714930 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714930
  have eq714954 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq714953
  have eq714994 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq714954
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq714954
    | exact resolve eq714954 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714954
  have eq717202 : x ≠ x ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq714994
       grind)
    | exact superpose eq714994 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq714994
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq714994
       grind)
    | exact resolve eq14 eq714994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq717203 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq714994
       grind)
    | exact superpose eq714994 eq56
    | (have j0 := eq56 y x
       grind)
    | (have r₁ := eq56 y x
       have r₂ := eq714994
       grind)
    | (have r₁ := eq56 x y
       have r₂ := eq714994
       grind)
    | exact resolve eq56 eq714994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714994
  have eq717204 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq717203
  have eq717205 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq717202
  have eq717207 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq717204
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq717204
    | exact resolve eq717204 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717204
  have eq717208 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq717207
       have r₂ := eq50
       grind)
    | exact resolve eq717207 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717207
  have eq717216 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq717208
       grind)
    | exact superpose eq717208 eq70
    | exact resolve eq70 eq717208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717208
  have eq717582 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq717216
    | exact resolve eq717216 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717216
  have eq720308 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq717205
       grind)
    | exact superpose eq717205 eq44
    | exact resolve eq44 eq717205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717205
  have eq720405 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq720308
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq720308
    | exact resolve eq720308 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720308
  have eq722669 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq720405 eq640160
    | exact resolve eq640160 eq720405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640160 eq720405
  have eq722692 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq722669
  have eq724911 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq722692 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | (have r₁ := eq56 (σ y) (σ x)
       have r₂ := eq722692
       grind)
    | (have r₁ := eq56 x y
       have r₂ := eq722692
       grind)
    | exact resolve eq56 eq722692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722692
  have eq724912 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq724911
  have eq724938 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq724912
    | exact resolve eq724912 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724912
  have eq727052 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq724938 eq717582
    | exact resolve eq717582 eq724938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717582 eq724938
  have eq727067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq727052
  have eq727319 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq727067
       have r₂ := eq27
       grind)
    | exact resolve eq727067 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727067
  have eq727329 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq727319 eq26
    | exact resolve eq26 eq727319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727331 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k y X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq727319 eq36
    | exact resolve eq36 eq727319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq727332 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq727319 eq40
    | exact resolve eq40 eq727319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq728010 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq727319 eq640157
    | (have r₁ := eq640157
       have r₂ := eq727319
       grind)
    | exact resolve eq640157 eq727319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640157
  have eq728128 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq728010
  have eq728129 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq728128
  have eq728697 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3545 eq728129
    | exact resolve eq728129 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3545 eq728129
  have eq728800 : ∀ X0 : G, (σ (k X0 x)) = (σ (k X0 y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq39 eq727332
    | exact resolve eq727332 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq727332
  have eq728801 : ∀ X0 : G, (σ (k x X0)) = (σ (k y X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq35 eq727331
    | exact resolve eq727331 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq727331
  have eq734738 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq727329 eq3551
    | exact resolve eq3551 eq727329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727329
  have eq734776 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq734738
       have i₂ := eq14235
       grind)
    | exact superpose eq14235 eq734738
    | exact resolve eq734738 eq14235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734738
  have eq734780 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq728697 eq3551
    | exact resolve eq3551 eq728697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3551
  have eq734781 : (k x (k x x)) = (τ (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq728697 eq4396
    | exact resolve eq4396 eq728697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4396 eq728697
  have eq734811 : (k x x) = (k x (k x x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49 eq734781
    | exact resolve eq734781 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq734781
  have eq734812 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq734780
       have i₂ := eq14235
       grind)
    | exact superpose eq14235 eq734780
    | exact resolve eq734780 eq14235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734780
  have eq734820 : (M.op x x) = (k x (M.op x x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq734811
       have i₂ := eq14235
       grind)
    | exact superpose eq14235 eq734811
    | exact resolve eq734811 eq14235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14235 eq734811
  have eq734821 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq734812
    | exact resolve eq734812 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734812
  have eq740151 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq734821
       have i₂ := eq734776
       grind)
    | exact superpose eq734776 eq734821
    | exact resolve eq734821 eq734776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734821
  have eq740165 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq740151
  have eq742216 : (k y x) = (τ (k (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq740165 eq249
    | exact resolve eq249 eq740165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq740165
  have eq767706 : (k y x) = (τ (k (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq727319 eq742216
    | exact resolve eq742216 eq727319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727319 eq742216
  have eq768223 : (k y x) = (τ (k (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq767706
  have eq771525 : (σ (k y x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq768223 eq15
    | exact resolve eq15 eq768223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768223
  have eq772019 : (k (σ y) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq771525
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq771525
    | exact resolve eq771525 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771525
  have eq775962 : ∀ X0 : G, (k X0 y) = (τ (σ (k X0 x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 y)
       have i₂ := eq728800 X0
       grind)
    | exact superpose eq728800 eq16
    | exact resolve eq16 eq728800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776479 : ∀ X0 : G, (k X0 x) = (k X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq775962 X0
       have i₂ := eq16 (k X0 x)
       grind)
    | exact superpose eq16 eq775962
    | exact resolve eq775962 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775962
  have eq782565 : (σ (k x y)) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq728800 y
       have i₂ := eq728801 y
       grind)
    | exact superpose eq728801 eq728800
    | exact resolve eq728800 eq728801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728800
  have eq782580 : ∀ X0 : G, (k y X0) = (τ (σ (k x X0))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 (k y X0)
       have i₂ := eq728801 X0
       grind)
    | exact superpose eq728801 eq16
    | exact resolve eq16 eq728801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728801
  have eq782854 : (σ (k x y)) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq782565
  have eq783105 : ∀ X0 : G, (k x X0) = (k y X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq782580 X0
       have i₂ := eq16 (k x X0)
       grind)
    | exact superpose eq16 eq782580
    | exact resolve eq782580 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782580
  have eq783118 : (σ (k x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq782854
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq782854
    | exact resolve eq782854 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782854
  have eq783279 : (k (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq783118
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq783118
    | exact resolve eq783118 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq783118
  have eq784436 : (k x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq776479 y
       have i₂ := eq783105 y
       grind)
    | exact superpose eq783105 eq776479
    | exact resolve eq776479 eq783105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776479 eq783105
  have eq784511 : (k x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq784436
  have eq788680 : (k (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq783279 eq772019
    | exact resolve eq772019 eq783279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772019 eq783279
  have eq788701 : (k (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq788680
  have eq801211 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq734820
       have i₂ := eq734776
       grind)
    | exact superpose eq734776 eq734820
    | exact resolve eq734820 eq734776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734776 eq734820
  have eq801240 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq801211
  have eq801256 : (τ (M.op (σ x) (σ y))) = (τ (k (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq801240
       have i₂ := eq226 sF4
       grind)
    | exact superpose eq226 eq801240
    | exact resolve eq801240 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq801240
  have eq801702 : (k (σ x) (M.op (σ x) (σ y))) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq801256 eq15
    | exact resolve eq15 eq801256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801256
  have eq802506 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq801702
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq801702
    | exact resolve eq801702 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801702
  have eq802560 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq802506 eq788701
    | exact resolve eq788701 eq802506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788701 eq802506
  have eq802619 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq802560
  have eq802689 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq802619 eq118
    | exact resolve eq118 eq802619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq802619
  have eq802773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq802689
  have eq802799 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq802773
       have r₂ := eq27
       grind)
    | exact resolve eq802773 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802773
  have eq803608 : x ≠ x ∨ x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq802799
       grind)
    | exact superpose eq802799 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq802799
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq802799
       grind)
    | exact resolve eq14 eq802799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq803609 : x ≠ x ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq802799
       grind)
    | exact superpose eq802799 eq56
    | (have j0 := eq56 y x
       grind)
    | (have r₁ := eq56 y x
       have r₂ := eq802799
       grind)
    | (have r₁ := eq56 x y
       have r₂ := eq802799
       grind)
    | exact resolve eq56 eq802799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802799
  have eq803610 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq803609
  have eq803611 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq803608
  have eq803614 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq803610
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq803610
    | exact resolve eq803610 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803610
  have eq803615 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq803614
       have r₂ := eq50
       grind)
    | exact resolve eq803614 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803614
  have eq803630 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq803615
       grind)
    | exact superpose eq803615 eq70
    | exact resolve eq70 eq803615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq803785 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq784511
       have i₂ := eq803615
       grind)
    | exact superpose eq803615 eq784511
    | exact resolve eq784511 eq803615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784511 eq803615
  have eq803817 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq803785
  have eq804019 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq803630
    | exact resolve eq803630 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803630
  have eq804936 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq803611
       have i₂ := eq803817
       grind)
    | exact superpose eq803817 eq803611
    | exact resolve eq803611 eq803817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803611 eq803817
  have eq804968 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq804936
  have eq805133 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq804968 eq50
    | (have r₁ := eq50
       have r₂ := eq804968
       grind)
    | exact resolve eq50 eq804968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805408 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq804968
  have eq805419 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq805133
  have eq807618 : (σ y) ≠ (σ y) ∨ (σ y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4114 y
       have i₂ := eq805419
       grind)
    | exact superpose eq805419 eq4114
    | (have j0 := eq4114 y
       grind)
    | exact resolve eq4114 eq805419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4114 eq805419
  have eq807653 : (σ y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq807618
  have eq807931 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq807653
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq807653
    | exact resolve eq807653 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807653
  have eq807980 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq807931
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq807931
    | exact resolve eq807931 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807931
  have eq808006 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq807980
    | exact resolve eq807980 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807980
  have eq808028 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq808006
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq808006
    | exact resolve eq808006 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808006
  have eq1024043 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq808028 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | (have r₁ := eq56 (σ y) (σ x)
       have r₂ := eq808028
       grind)
    | (have r₁ := eq56 (σ x) (σ y)
       have r₂ := eq808028
       grind)
    | exact resolve eq56 eq808028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808028
  have eq1024044 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1024043
  have eq1024072 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1024044
    | exact resolve eq1024044 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024044
  have eq1024075 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1024072
       have r₂ := eq51
       grind)
    | exact resolve eq1024072 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1024072
  have eq1024383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1024075 eq804019
    | exact resolve eq804019 eq1024075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804019 eq1024075
  have eq1024496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1024383
  have eq1024791 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1024496
       have r₂ := eq27
       grind)
    | exact resolve eq1024496 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024496
  have eq1024823 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1024791 eq29
    | exact resolve eq29 eq1024791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024791
  have eq1026813 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq1024823
    | exact resolve eq1024823 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1024823
  have eq1026855 : x = (M.op x y) := by
    first
    | (have r₁ := eq1026813
       have r₂ := eq805408
       grind)
    | exact resolve eq1026813 eq805408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805408 eq1026813
  have eq1026892 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1026855 eq20
    | exact resolve eq20 eq1026855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1026894 : x ≠ y ∨ x = (k y x) := by
    first
    | exact superpose eq1026855 eq50
    | exact resolve eq50 eq1026855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1026899 : x ≠ x ∨ x = y ∨ x = (M.op y x) ∨ y = (k x y) := by
    first
    | exact superpose eq1026855 eq78
    | (have r₁ := eq78
       have r₂ := eq1026855
       grind)
    | exact resolve eq78 eq1026855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1027286 : y = (k x y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq1026899
  have eq1027645 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1026892
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1026892
    | exact resolve eq1026892 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026892
  have eq1027699 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1027645 eq26
    | exact resolve eq26 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1028675 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1027699 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq1027699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1036049 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3517 y
       have i₂ := eq1027286
       grind)
    | exact superpose eq1027286 eq3517
    | (have j0 := eq3517 y
       grind)
    | exact resolve eq3517 eq1027286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3517
  have eq1036051 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3549 y
       have i₂ := eq1027286
       grind)
    | exact superpose eq1027286 eq3549
    | (have j0 := eq3549 y
       grind)
    | exact resolve eq3549 eq1027286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3549
  have eq1036069 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq1036051
  have eq1036070 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq1036049
  have eq1036101 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1027645 eq1036069
    | exact resolve eq1036069 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036069
  have eq1036103 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1036070
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1036070
    | exact resolve eq1036070 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036070
  have eq1036190 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1036101
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1036101
    | exact resolve eq1036101 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036101
  have eq1036192 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq26 eq1036103
    | exact resolve eq1036103 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036103
  have eq1036276 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1036190
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1036190
    | exact resolve eq1036190 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036190
  have eq1036278 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1036192
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1036192
    | exact resolve eq1036192 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036192
  have eq1036337 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq26 eq1036276
    | exact resolve eq1036276 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036276
  have eq1036339 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq26 eq1036278
    | exact resolve eq1036278 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036278
  have eq1036366 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1027645 eq1036337
    | exact resolve eq1036337 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036337
  have eq1036368 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1027645 eq1036339
    | exact resolve eq1036339 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036339
  have eq1036390 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq1036366
       have r₂ := eq27
       grind)
    | exact resolve eq1036366 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036366
  have eq1036392 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq1036368
       have r₂ := eq27
       grind)
    | exact resolve eq1036368 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036368
  have eq1036407 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1027645 eq1036392
    | exact resolve eq1036392 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036392
  have eq1036420 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1036407
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1036407
    | exact resolve eq1036407 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036407
  have eq1398980 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1036420 eq1036390
    | exact resolve eq1036390 eq1036420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036390
  have eq1398981 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1036420 eq14
    | (have r₁ := eq14 (σ (M.op x y)) (σ y)
       have r₂ := eq1036420
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq1036420
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq1036420
       grind)
    | exact resolve eq14 eq1036420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036420
  have eq1398984 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq1398981
  have eq1398985 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1398980
  have eq1399127 : x ≠ x ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq1398985
       grind)
    | exact superpose eq1398985 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq1398985
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq1398985
       grind)
    | exact resolve eq14 eq1398985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1399128 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq1398985
       grind)
    | exact superpose eq1398985 eq56
    | (have j0 := eq56 y x
       grind)
    | (have r₁ := eq56 y x
       have r₂ := eq1398985
       grind)
    | (have r₁ := eq56 (σ x) (σ y)
       have r₂ := eq1398985
       grind)
    | exact resolve eq56 eq1398985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398985
  have eq1399129 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1399128
  have eq1399130 : x = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1399127
  have eq1399133 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1399129
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1399129
    | exact resolve eq1399129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399129
  have eq1399134 : x = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1026855 eq1399133
    | exact resolve eq1399133 eq1026855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399133
  have eq1399135 : x = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1399134
       have r₂ := eq1026894
       grind)
    | exact resolve eq1399134 eq1026894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399134
  have eq1399541 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3717 x
       have i₂ := eq1399135
       grind)
    | exact superpose eq1399135 eq3717
    | (have j0 := eq3717 x
       grind)
    | exact resolve eq3717 eq1399135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3717 eq1399135
  have eq1399562 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1399541
  have eq1399675 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1399562
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1399562
    | exact resolve eq1399562 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399562
  have eq1399765 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1399675
    | exact resolve eq1399675 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399675
  have eq1399852 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1027645 eq1399765
    | exact resolve eq1399765 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399765
  have eq1399928 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1399852
       have r₂ := eq27
       grind)
    | exact resolve eq1399852 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399852
  have eq1399972 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1399928
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1399928
    | exact resolve eq1399928 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399928
  have eq1399987 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1027645 eq1399972
    | exact resolve eq1399972 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399972
  have eq1401179 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4321 x
       have i₂ := eq1399130
       grind)
    | exact superpose eq1399130 eq4321
    | (have j0 := eq4321 x
       grind)
    | exact resolve eq4321 eq1399130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4321 eq1399130
  have eq1401213 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1401179
  have eq1401250 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1401213
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1401213
    | exact resolve eq1401213 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401213
  have eq1401346 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1027645 eq1401250
    | exact resolve eq1401250 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401250
  have eq1401347 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1401346
  have eq1401446 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1401347
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1401347
    | exact resolve eq1401347 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401347
  have eq1401528 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1027645 eq1401446
    | exact resolve eq1401446 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401446
  have eq1401578 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1401528
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1401528
    | exact resolve eq1401528 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401528
  have eq1401600 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1401578
    | exact resolve eq1401578 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401578
  have eq1401601 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1401600
  have eq1401944 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1401601 eq1399987
    | exact resolve eq1399987 eq1401601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399987 eq1401601
  have eq1401951 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1401944
  have eq1402439 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1401951 eq1028675
    | (have r₁ := eq1028675
       have r₂ := eq1401951
       grind)
    | exact resolve eq1028675 eq1401951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401951
  have eq1402442 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1402439
  have eq1402608 : (τ (σ y)) = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1402442 eq89
    | exact resolve eq89 eq1402442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq1402442
  have eq1402777 : (τ (σ y)) = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1026855 eq1402608
    | exact resolve eq1402608 eq1026855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402608
  have eq1402818 : y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq1402777
    | exact resolve eq1402777 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1402777
  have eq1442867 : (τ (σ (M.op x y))) = (k (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1398984 eq159
    | exact resolve eq159 eq1398984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq1398984
  have eq1443038 : (τ (σ (M.op x y))) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1026855 eq1442867
    | exact resolve eq1442867 eq1026855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442867
  have eq1443082 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq30 eq1443038
    | exact resolve eq1443038 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1443038
  have eq1443108 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1026855 eq1443082
    | exact resolve eq1443082 eq1026855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443082
  have eq1443205 : x = y ∨ x = (M.op y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1027286
       have i₂ := eq1443108
       grind)
    | exact superpose eq1443108 eq1027286
    | exact resolve eq1027286 eq1443108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027286 eq1443108
  have eq1443262 : x = (M.op y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1443205
  have eq1443738 : x ≠ x ∨ x = (k x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq1443262
       grind)
    | exact superpose eq1443262 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq1443262
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq1443262
       grind)
    | exact resolve eq14 eq1443262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1443739 : x ≠ x ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq1443262
       grind)
    | exact superpose eq1443262 eq56
    | (have j0 := eq56 y x
       grind)
    | (have r₁ := eq56 y x
       have r₂ := eq1443262
       grind)
    | (have r₁ := eq56 (σ x) (σ y)
       have r₂ := eq1443262
       grind)
    | exact resolve eq56 eq1443262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443262
  have eq1443740 : (M.op x y) = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1443739
  have eq1443741 : x = (k x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1443738
  have eq1443744 : (M.op x y) = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1443740
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1443740
    | exact resolve eq1443740 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443740
  have eq1443745 : x = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1026855 eq1443744
    | exact resolve eq1443744 eq1026855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443744
  have eq1443746 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1443745
       have r₂ := eq1026894
       grind)
    | exact resolve eq1443745 eq1026894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443745
  have eq1443768 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq1443746
       grind)
    | exact superpose eq1443746 eq70
    | exact resolve eq70 eq1443746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443746
  have eq1444382 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1027645 eq1443768
    | exact resolve eq1443768 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443768
  have eq1444470 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1444382
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1444382
    | exact resolve eq1444382 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444382
  have eq1444549 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1027645 eq1444470
    | exact resolve eq1444470 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444470
  have eq1445091 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4277 x
       have i₂ := eq1443741
       grind)
    | exact superpose eq1443741 eq4277
    | (have j0 := eq4277 x
       grind)
    | exact resolve eq4277 eq1443741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4277 eq1443741
  have eq1445127 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1445091
  have eq1445164 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1445127
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1445127
    | exact resolve eq1445127 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445127
  have eq1445260 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1445164
    | exact resolve eq1445164 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445164
  have eq1445261 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq1445260
  have eq1445358 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1445261
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1445261
    | exact resolve eq1445261 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445261
  have eq1445443 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq1445358
    | exact resolve eq1445358 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1445358
  have eq1445496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq1027645 eq1445443
    | exact resolve eq1445443 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445443
  have eq1445523 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq1445496
       have r₂ := eq27
       grind)
    | exact resolve eq1445496 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445496
  have eq1445543 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1445523
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1445523
    | exact resolve eq1445523 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445523
  have eq1445560 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1027645 eq1445543
    | exact resolve eq1445543 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445543
  have eq1445926 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1445560 eq56
    | (have j0 := eq56 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq56 (σ y) (σ (M.op x y))
       have r₂ := eq1445560
       grind)
    | (have r₁ := eq56 (σ x) (σ y)
       have r₂ := eq1445560
       grind)
    | exact resolve eq56 eq1445560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445560
  have eq1445927 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1445926
  have eq1445937 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1027699 eq1445927
    | exact resolve eq1445927 eq1027699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445927
  have eq1445938 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq1445937
       have r₂ := eq1028675
       grind)
    | exact resolve eq1445937 eq1028675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028675 eq1445937
  have eq1446035 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1445938 eq1444549
    | exact resolve eq1444549 eq1445938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444549 eq1445938
  have eq1446078 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq1446035
       have r₂ := eq27
       grind)
    | exact resolve eq1446035 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446035
  have eq1446103 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq1446078 eq27
    | exact resolve eq27 eq1446078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446078
  have eq1458571 : y ≠ y ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5937 y x
       have i₂ := eq1402818
       grind)
    | exact superpose eq1402818 eq5937
    | (have j0 := eq5937 y x
       grind)
    | (have r₁ := eq5937 y x
       have r₂ := eq1402818
       grind)
    | exact resolve eq5937 eq1402818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5937
  have eq1459156 : y ≠ y ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1458571
  have eq1459157 : y = (M.op x y) ∨ x = y ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1459156
  have eq1459211 : y = (M.op x y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1459157
       have r₂ := eq1446103
       grind)
    | exact resolve eq1459157 eq1446103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459157
  have eq1459313 : y = (M.op x y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1459211
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1459211
    | exact resolve eq1459211 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459211
  have eq1459391 : x = y ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq1026855 eq1459313
    | exact resolve eq1459313 eq1026855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459313
  have eq1459392 : x = (M.op y x) ∨ x = y := by grind
  clear eq1459391
  have eq1459504 : x ≠ x ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq1459392
       grind)
    | exact superpose eq1459392 eq56
    | (have j0 := eq56 y x
       grind)
    | (have r₁ := eq56 y x
       have r₂ := eq1459392
       grind)
    | exact resolve eq56 eq1459392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1459392
  have eq1459505 : (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq1459504
  have eq1459509 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq1459505
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1459505
    | exact resolve eq1459505 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1459505
  have eq1459510 : x = (k y x) ∨ x = y := by
    first
    | exact superpose eq1026855 eq1459509
    | exact resolve eq1459509 eq1026855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026855 eq1459509
  have eq1459511 : x = (k y x) := by
    first
    | (have r₁ := eq1459510
       have r₂ := eq1026894
       grind)
    | exact resolve eq1459510 eq1026894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026894 eq1459510
  have eq1459535 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq1459511
       grind)
    | exact superpose eq1459511 eq70
    | exact resolve eq70 eq1459511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1459917 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1402818
       have i₂ := eq1459511
       grind)
    | exact superpose eq1459511 eq1402818
    | exact resolve eq1402818 eq1459511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402818 eq1459511
  have eq1459962 : x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1459917
  have eq1460007 : x = y := by
    first
    | (have r₁ := eq1459962
       have r₂ := eq1446103
       grind)
    | exact resolve eq1459962 eq1446103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446103 eq1459962
  have eq1460075 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1027645 eq1459535
    | exact resolve eq1459535 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1459535
  have eq1460168 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1460075
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1460075
    | exact resolve eq1460075 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460075
  have eq1460247 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1027645 eq1460168
    | exact resolve eq1460168 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460168
  have eq1460366 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1460007
       grind)
    | exact superpose eq1460007 eq24
    | exact resolve eq24 eq1460007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1460007
  have eq1461974 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1460366
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1460366
    | exact resolve eq1460366 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1460366
  have eq1462357 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1027645 eq1461974
    | exact resolve eq1461974 eq1027645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027645 eq1461974
  have eq1463782 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1462357 eq1027699
    | exact resolve eq1027699 eq1462357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027699
  have eq1464600 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1462357 eq1460247
    | exact resolve eq1460247 eq1462357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460247 eq1462357
  have eq1464601 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3896 eq1464600
    | exact resolve eq1464600 eq3896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896 eq1464600
  have eq1465436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1464601 eq1463782
    | exact resolve eq1463782 eq1464601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463782 eq1464601
  have eq1465437 : False := by grind
  exact eq1465437

/-- `x □ y = if m(Y,X) = X then X else if m(X,Y) = Y then m(Y,X) else if m(X,Y) = X then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyx_x_pxy_y_pxy_x_x_pyx_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : y ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq73 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq55
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq55
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq91
    | exact resolve eq91 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq97 : (σ y) = (M.op (σ x) (σ y)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq94
    | exact resolve eq94 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq99 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq97
    | exact resolve eq97 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq100 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq107 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq118 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq143 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq126 eq16
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq165 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq643 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq79 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq79 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq79 X0 X0
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq79 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq79 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq13 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq79 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq649 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq648 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq650 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq644 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq651 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq643 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq653 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq650 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq650 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq650 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq650 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | exact resolve eq650 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq654 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq651 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq651 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq651 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq651 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq651 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq664 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq653 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq653
    | (have j0 := eq653 X0 X1
       grind)
    | exact resolve eq653 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq665 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq654 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq654
    | (have j0 := eq654 X0 X1
       grind)
    | exact resolve eq654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq666 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq665 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq2862 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq649 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq649
    | (have j0 := eq649 (τ X0)
       grind)
    | exact resolve eq649 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq649
  have eq2870 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2862 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2862
    | (have j0 := eq2862 X0
       grind)
    | exact resolve eq2862 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862
  have eq2876 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2870 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2870
    | (have j0 := eq2870 X0
       grind)
    | exact resolve eq2870 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2870
  have eq3352 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (k (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq165 eq12
    | (have j0 := eq12 (σ X0) (σ x)
       have j1 := eq165 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq165 x
       grind)
    | (have r₁ := eq12 (σ X0) (σ x)
       have r₂ := eq165 X0
       grind)
    | exact resolve eq12 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3353 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (k (σ X0) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq165 eq13
    | (have j0 := eq13 (σ X0) (σ x)
       have j1 := eq165 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ x)
       have r₂ := eq165 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq165 x
       grind)
    | (have r₁ := eq13 (σ x) (σ X0)
       have r₂ := eq165 X0
       grind)
    | exact resolve eq13 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq3357 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (k (σ X0) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq3353 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353
  have eq3358 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (k (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq3352 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352
  have eq3361 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (k (σ X0) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq3357 X0
       have j1 := eq13 (σ X0) (σ x)
       grind)
    | (have r₁ := eq3357 X0
       have r₂ := eq13 (σ x) (σ X0)
       grind)
    | (have r₁ := eq3357 X0
       have r₂ := eq13 (σ X0) (σ x)
       grind)
    | (have r₁ := eq3357 x
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq3357 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357
  have eq3362 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (k (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq3358 X0
       have j1 := eq12 (σ X0) (σ x)
       grind)
    | (have r₁ := eq3358 x
       have r₂ := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq3358 X0
       have r₂ := eq12 (σ X0) (σ x)
       grind)
    | exact resolve eq3358 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358
  have eq3382 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq39 eq3361
    | (have j0 := eq3361 X0
       grind)
    | exact resolve eq3361 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3361
  have eq3383 : ∀ X0 : G, (σ x) = (σ (k X0 x)) ∨ (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq39 eq3362
    | (have j0 := eq3362 X0
       grind)
    | exact resolve eq3362 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq3362
  have eq3384 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq3383 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383
  have eq3538 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq187 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq7849 : (σ x) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq664 y x
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq664
    | (have j0 := eq664 y x
       grind)
    | exact resolve eq664 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq7890 : (σ x) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7849
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7849
    | exact resolve eq7849 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7849
  have eq7977 : (k (σ y) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7890
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7890
    | exact resolve eq7890 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7890
  have eq8064 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7977
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7977
    | exact resolve eq7977 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7977
  have eq8149 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq8064
    | exact resolve eq8064 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8064
  have eq8232 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8149
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8149
    | exact resolve eq8149 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8149
  have eq8314 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8232
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8232
    | exact resolve eq8232 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8232
  have eq8396 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq8314
    | exact resolve eq8314 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8314
  have eq8463 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8396
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8396
    | exact resolve eq8396 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8396
  have eq8472 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8463
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8463
    | exact resolve eq8463 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8463
  have eq18327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18328 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq18327
    | exact resolve eq18327 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18327
  have eq18339 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq18328
       have r₂ := eq27
       grind)
    | exact resolve eq18328 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18328
  have eq18341 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq18339
    | exact resolve eq18339 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18339
  have eq18343 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq18341
    | exact resolve eq18341 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18341
  have eq18346 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq18343 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq18343
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq18343
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq18343
       grind)
    | exact resolve eq14 eq18343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18343
  have eq18347 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq18346
  have eq18356 : (τ (σ x)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq18347 eq55
    | exact resolve eq55 eq18347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18347
  have eq18383 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq18356
    | exact resolve eq18356 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18356
  have eq18386 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq18383
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq18383
       have r₂ := eq14 y x
       grind)
    | (have r₁ := eq18383
       have r₂ := eq14 x y
       grind)
    | exact resolve eq18383 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18383
  have eq18403 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq647 x y
       have i₂ := eq18386
       grind)
    | exact superpose eq18386 eq647
    | (have j0 := eq647 x y
       grind)
    | exact resolve eq647 eq18386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18407 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18386
       grind)
    | exact superpose eq18386 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18386
  have eq18408 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18407
  have eq18410 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18403
  have eq18413 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18408
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18408
    | exact resolve eq18408 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18408
  have eq18414 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq18413
  have eq18418 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18410
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18410
    | exact resolve eq18410 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18410
  have eq18431 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18414
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18414
    | exact resolve eq18414 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18414
  have eq18432 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18431
  have eq18436 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18418
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18418
    | exact resolve eq18418 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18418
  have eq18443 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18436
    | exact resolve eq18436 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18436
  have eq18444 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18443
  have eq18449 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18444
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18444
    | exact resolve eq18444 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18444
  have eq18455 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18449
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18449
    | exact resolve eq18449 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18449
  have eq18460 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18455
    | exact resolve eq18455 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18455
  have eq18461 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18460
  have eq18467 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18461
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18461
    | exact resolve eq18461 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18461
  have eq18474 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18467
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18467
    | exact resolve eq18467 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18467
  have eq18523 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18432
       grind)
    | exact superpose eq18432 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18432
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18432
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18432
       grind)
    | exact resolve eq13 eq18432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18432
  have eq18526 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18523
  have eq18527 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18526
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18526
    | exact resolve eq18526 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18526
  have eq18528 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18527
  have eq18529 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18528
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18528
    | exact resolve eq18528 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18528
  have eq18539 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18474 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18474
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18474
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18474
       grind)
    | exact resolve eq13 eq18474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18474
  have eq18542 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18539
  have eq18543 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18542
    | exact resolve eq18542 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18542
  have eq18544 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18543
  have eq18545 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18544
    | exact resolve eq18544 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18544
  have eq18811 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq18529
       grind)
    | exact superpose eq18529 eq71
    | exact resolve eq71 eq18529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18529
  have eq18839 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq18811
    | exact resolve eq18811 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18811
  have eq19161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18839 eq18545
    | exact resolve eq18545 eq18839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18545 eq18839
  have eq19168 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19161
  have eq19170 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19168
       have r₂ := eq27
       grind)
    | exact resolve eq19168 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19168
  have eq19182 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19170 eq51
    | (have r₁ := eq51
       have r₂ := eq19170
       grind)
    | exact resolve eq51 eq19170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19170
  have eq19185 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19182
  have eq19721 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19185 eq78
    | exact resolve eq78 eq19185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19185
  have eq19753 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq19721
    | exact resolve eq19721 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19721
  have eq19758 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19753
       have r₂ := eq50
       grind)
    | exact resolve eq19753 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19753
  have eq19761 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq19758
       grind)
    | exact superpose eq19758 eq71
    | exact resolve eq71 eq19758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19772 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq647 y x
       have i₂ := eq19758
       grind)
    | exact superpose eq19758 eq647
    | (have j0 := eq647 y x
       grind)
    | exact resolve eq647 eq19758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq19774 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq666 y x
       have i₂ := eq19758
       grind)
    | exact superpose eq19758 eq666
    | (have j0 := eq666 y x
       grind)
    | exact resolve eq666 eq19758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq19776 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq19758
       grind)
    | exact superpose eq19758 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq19758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19777 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19776
  have eq19778 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19774
  have eq19779 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19772
  have eq19784 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19777
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19777
    | exact resolve eq19777 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19777
  have eq19786 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19778
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19778
    | exact resolve eq19778 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19778
  have eq19788 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19779
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19779
    | exact resolve eq19779 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19779
  have eq19798 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19761
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19761
    | exact resolve eq19761 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19761
  have eq19801 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19786
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19786
    | exact resolve eq19786 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19786
  have eq19803 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19788
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19788
    | exact resolve eq19788 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19788
  have eq19806 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19801
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19801
    | exact resolve eq19801 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19801
  have eq19808 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19803
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19803
    | exact resolve eq19803 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19803
  have eq19811 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19806
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19806
    | exact resolve eq19806 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19806
  have eq19813 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19808
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19808
    | exact resolve eq19808 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19808
  have eq19816 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19811
    | exact resolve eq19811 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19811
  have eq19818 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19813
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19813
    | exact resolve eq19813 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19813
  have eq19821 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19816
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19816
    | exact resolve eq19816 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19816
  have eq19823 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19818
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19818
    | exact resolve eq19818 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19818
  have eq19826 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19821
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19821
    | exact resolve eq19821 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19821
  have eq19828 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19823
    | exact resolve eq19823 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19823
  have eq24042 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19826 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19826
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19826
       grind)
    | exact resolve eq13 eq19826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19826
  have eq24045 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24042
  have eq24046 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq24045
    | exact resolve eq24045 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24045
  have eq24047 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24046
  have eq24048 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq24047
    | exact resolve eq24047 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24047
  have eq25075 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24048 eq19798
    | exact resolve eq19798 eq24048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24048
  have eq25086 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq25075
  have eq35634 : y ≠ y ∨ x = y ∨ y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19784
       grind)
    | exact superpose eq19784 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq19784
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq19784
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq19784
       grind)
    | exact resolve eq12 eq19784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35637 : x ≠ y ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19784
  have eq35638 : x = y ∨ y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq35634
  have eq35642 : y = (M.op x y) ∨ x = y ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35638
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35638
    | exact resolve eq35638 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35638
  have eq35643 : y = (M.op x y) ∨ x = y ∨ x = (k y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq35642
  have eq36247 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19828 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19828
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19828
       grind)
    | exact resolve eq13 eq19828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19828
  have eq36256 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq36247
       have r₂ := eq25086
       grind)
    | exact resolve eq36247 eq25086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25086 eq36247
  have eq36258 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq36256
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq36256
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq36256 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36256
  have eq36259 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq36258
    | exact resolve eq36258 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36258
  have eq36260 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq36259
  have eq36261 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq36260
    | exact resolve eq36260 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36260
  have eq36592 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36261 eq19798
    | exact resolve eq19798 eq36261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19798 eq36261
  have eq36627 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq36592
  have eq36641 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36627 eq27
    | exact resolve eq27 eq36627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36627
  have eq405079 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq35643
       have r₂ := eq35637
       grind)
    | exact resolve eq35643 eq35637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35643
  have eq406549 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19758
       have i₂ := eq405079
       grind)
    | exact superpose eq405079 eq19758
    | exact resolve eq19758 eq405079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405079
  have eq406980 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq406549
  have eq407014 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq406980
       have r₂ := eq35637
       grind)
    | exact resolve eq406980 eq35637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35637 eq406980
  have eq407122 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq407014
       grind)
    | exact superpose eq407014 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq407014
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq407014
       grind)
    | exact resolve eq13 eq407014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407014
  have eq407125 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq407122
  have eq407127 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq407125
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq407125
    | exact resolve eq407125 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407125
  have eq407128 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq407127
  have eq407129 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq407128
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq407128
    | exact resolve eq407128 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407128
  have eq408780 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19758
       have i₂ := eq407129
       grind)
    | exact superpose eq407129 eq19758
    | exact resolve eq19758 eq407129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19758 eq407129
  have eq409202 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq408780
  have eq409388 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq409202 eq27
    | exact resolve eq27 eq409202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409389 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq409202 eq51
    | exact resolve eq51 eq409202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409391 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq409202 eq65
    | (have r₁ := eq65
       have r₂ := eq409202
       grind)
    | exact resolve eq65 eq409202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq409392 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq409391
  have eq413711 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq409392 eq55
    | exact resolve eq55 eq409392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq413797 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq413711
    | exact resolve eq413711 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413711
  have eq413813 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq413797 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq413797
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq413797
       grind)
    | exact resolve eq14 eq413797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413797
  have eq413814 : (σ x) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq413813
  have eq413826 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq413814 eq101
    | exact resolve eq101 eq413814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413814
  have eq413880 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq413826
  have eq413894 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq413880
       have r₂ := eq409388
       grind)
    | exact resolve eq413880 eq409388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409388 eq413880
  have eq413899 : y = (k x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq413894
       have r₂ := eq64
       grind)
    | exact resolve eq413894 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413894
  have eq413941 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq413899
       grind)
    | exact superpose eq413899 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq413899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413899
  have eq413958 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq413941
  have eq413980 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq413958
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq413958
    | exact resolve eq413958 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413958
  have eq413981 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq413980
  have eq414029 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq413981
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq413981
    | exact resolve eq413981 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413981
  have eq414126 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq414029
       grind)
    | exact superpose eq414029 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq414029
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq414029
       grind)
    | exact resolve eq13 eq414029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414127 : x ≠ x ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq414029
       grind)
    | exact superpose eq414029 eq14
    | (have j0 := eq14 x y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq414029
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq414029
       grind)
    | exact resolve eq14 eq414029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414029
  have eq414128 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq414127
  have eq414129 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq414126
  have eq414131 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq414129
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq414129
    | exact resolve eq414129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414129
  have eq414132 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq414131
  have eq414133 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq414132
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq414132
    | exact resolve eq414132 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414132
  have eq414138 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq414128
       grind)
    | exact superpose eq414128 eq44
    | exact resolve eq44 eq414128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414128
  have eq414252 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq414138
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq414138
    | exact resolve eq414138 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414138
  have eq414356 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq414133
       grind)
    | exact superpose eq414133 eq71
    | exact resolve eq71 eq414133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414133
  have eq415029 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq414356
    | exact resolve eq414356 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414356
  have eq415171 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq414252 eq409392
    | exact resolve eq409392 eq414252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409392 eq414252
  have eq415204 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq415171
  have eq415963 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq415204 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq415204
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq415204
       grind)
    | exact resolve eq13 eq415204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415204
  have eq415966 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq415963
  have eq415968 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq415966
    | exact resolve eq415966 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415966
  have eq415969 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq415968
    | exact resolve eq415968 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415968
  have eq416307 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq415969 eq415029
    | exact resolve eq415029 eq415969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415029 eq415969
  have eq416329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq416307
  have eq416558 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq416329
       have r₂ := eq27
       grind)
    | exact resolve eq416329 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416329
  have eq418153 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq416558 eq51
    | (have r₁ := eq51
       have r₂ := eq416558
       grind)
    | exact resolve eq51 eq416558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq418155 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq416558 eq409202
    | exact resolve eq409202 eq416558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409202
  have eq418156 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq418155
  have eq418158 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq418153
  have eq418160 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq418158
       have r₂ := eq409389
       grind)
    | exact resolve eq418158 eq409389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409389 eq418158
  have eq418162 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq418156 eq29
    | exact resolve eq29 eq418156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418163 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k y X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq418156 eq36
    | exact resolve eq36 eq418156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq418170 : (τ (k (σ x) (σ x))) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq418156 eq78
    | exact resolve eq78 eq418156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418175 : (τ (k (σ x) (σ x))) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq418156 eq107
    | exact resolve eq107 eq418156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418156
  have eq418936 : (k x x) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49 eq418175
    | exact resolve eq418175 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418175
  have eq418939 : (k x x) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49 eq418170
    | exact resolve eq418170 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq418170
  have eq418946 : ∀ X0 : G, (σ (k x X0)) = (σ (k y X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq35 eq418163
    | exact resolve eq418163 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq418163
  have eq418947 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq418162
    | exact resolve eq418162 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq418162
  have eq420328 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq418947 eq20
    | exact resolve eq20 eq418947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418947
  have eq420738 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq420328
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq420328
    | exact resolve eq420328 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420328
  have eq420982 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq420738 eq36641
    | (have r₁ := eq36641
       have r₂ := eq420738
       grind)
    | exact resolve eq36641 eq420738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36641
  have eq421356 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq420982
  have eq421357 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq421356
  have eq421579 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq421357 eq27
    | exact resolve eq27 eq421357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421357
  have eq423012 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq418160 eq78
    | exact resolve eq78 eq418160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq423025 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq418160 eq8472
    | exact resolve eq8472 eq418160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8472 eq418160
  have eq423151 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq423025
  have eq423169 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq423151
       have r₂ := eq416558
       grind)
    | exact resolve eq423151 eq416558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423151
  have eq423178 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq423012
    | exact resolve eq423012 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423012
  have eq423185 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq423178
       have r₂ := eq50
       grind)
    | exact resolve eq423178 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423178
  have eq423191 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq423185
       grind)
    | exact superpose eq423185 eq71
    | exact resolve eq71 eq423185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423249 : (σ y) ≠ (σ y) ∨ (σ y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3384 y
       have i₂ := eq423185
       grind)
    | exact superpose eq423185 eq3384
    | (have j0 := eq3384 y
       grind)
    | exact resolve eq3384 eq423185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423292 : (σ y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq423249
  have eq423371 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq423292
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq423292
    | exact resolve eq423292 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423292
  have eq423389 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq423191
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq423191
    | exact resolve eq423191 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423191
  have eq423418 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq423371
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq423371
    | exact resolve eq423371 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423371
  have eq423448 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq423418
    | exact resolve eq423418 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423418
  have eq423475 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq423448
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq423448
    | exact resolve eq423448 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423448
  have eq427521 : (σ (k x x)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq418936
       grind)
    | exact superpose eq418936 eq72
    | exact resolve eq72 eq418936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq418936
  have eq427631 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq427521
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq427521
    | exact resolve eq427521 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427521
  have eq427942 : y = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq423185
       have i₂ := eq418939
       grind)
    | exact superpose eq418939 eq423185
    | exact resolve eq423185 eq418939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418939
  have eq427992 : y = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq427942
  have eq428418 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43
       have i₂ := eq427992
       grind)
    | exact superpose eq427992 eq43
    | exact resolve eq43 eq427992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq427992
  have eq428521 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq428418
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq428418
    | exact resolve eq428418 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428418
  have eq431831 : (σ y) ≠ (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq427631 eq2876
    | (have j0 := eq2876 (σ y)
       grind)
    | exact resolve eq2876 eq427631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2876 eq427631
  have eq431877 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq431831
       have r₂ := eq428521
       grind)
    | exact resolve eq431831 eq428521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428521 eq431831
  have eq431893 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq431877 eq14
    | (have j0 := eq14 (σ y) (σ y)
       grind)
    | (have r₁ := eq14 (σ y) (σ y)
       have r₂ := eq431877
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq431877
       grind)
    | exact resolve eq14 eq431877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431877
  have eq431894 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq431893
  have eq431909 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq431894 eq107
    | exact resolve eq107 eq431894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq431894
  have eq431994 : y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq431909
    | exact resolve eq431909 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431909
  have eq440535 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq423169 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq423169
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq423169
       grind)
    | exact resolve eq13 eq423169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423169
  have eq440554 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq440535
       have r₂ := eq416558
       grind)
    | exact resolve eq440535 eq416558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416558 eq440535
  have eq440557 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq440554
    | exact resolve eq440554 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440554
  have eq440558 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq440557
  have eq440559 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq440558
    | exact resolve eq440558 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440558
  have eq451055 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq423475 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq423475
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq423475
       grind)
    | exact resolve eq13 eq423475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423475
  have eq451058 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq451055
  have eq451063 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq451058
    | exact resolve eq451058 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451058
  have eq451064 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq451063
  have eq451066 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq451064
    | exact resolve eq451064 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451064
  have eq452689 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq440559 eq423389
    | exact resolve eq423389 eq440559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440559
  have eq452721 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq452689
  have eq452971 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq452721 eq27
    | exact resolve eq27 eq452721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452721
  have eq455350 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq451066 eq423389
    | exact resolve eq423389 eq451066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423389 eq451066
  have eq455382 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq455350
  have eq455849 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq455382 eq27
    | exact resolve eq27 eq455382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455382
  have eq455861 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq420738 eq455849
    | (have r₁ := eq455849
       have r₂ := eq420738
       grind)
    | exact resolve eq455849 eq420738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420738 eq455849
  have eq455862 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq455861
  have eq455863 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq455862
  have eq455864 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq455863
       have r₂ := eq421579
       grind)
    | exact resolve eq455863 eq421579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421579 eq455863
  have eq455871 : x ≠ x ∨ x = y ∨ x = (M.op y x) ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq455864 eq64
    | (have r₁ := eq64
       have r₂ := eq455864
       grind)
    | exact resolve eq64 eq455864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq455878 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq455864 eq118
    | exact resolve eq118 eq455864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq456052 : x ≠ x ∨ x = y ∨ x = (M.op y x) ∨ y = (k x y) := by grind
  clear eq455871
  have eq456053 : y = (k x y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq456052
  have eq456193 : ∀ X0 : G, (k (σ x) X0) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq455878 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq455878
    | exact resolve eq455878 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq455878
  have eq514691 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq456053
       grind)
    | exact superpose eq456053 eq44
    | exact resolve eq44 eq456053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514807 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq514691
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq514691
    | exact resolve eq514691 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514691
  have eq515015 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq514807 eq456193
    | exact resolve eq456193 eq514807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456193 eq514807
  have eq515035 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq515015
  have eq846716 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq418946 y
       have i₂ := eq431994
       grind)
    | exact superpose eq431994 eq418946
    | exact resolve eq418946 eq431994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418946 eq431994
  have eq847357 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq846716
  have eq847769 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq847357
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq847357
    | exact resolve eq847357 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847357
  have eq847861 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq847769
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq847769
    | exact resolve eq847769 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847769
  have eq848047 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq847861 eq101
    | exact resolve eq101 eq847861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq847861
  have eq848145 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq848047
  have eq848175 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq848145
       have r₂ := eq452971
       grind)
    | exact resolve eq848145 eq452971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452971 eq848145
  have eq848184 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq848175
       grind)
    | exact superpose eq848175 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq848175
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq848175
       grind)
    | exact resolve eq13 eq848175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848175
  have eq848187 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq848184
  have eq848189 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq848187
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq848187
    | exact resolve eq848187 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848187
  have eq848190 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq848189
  have eq848191 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq848190
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq848190
    | exact resolve eq848190 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848190
  have eq849121 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq423185
       have i₂ := eq848191
       grind)
    | exact superpose eq848191 eq423185
    | exact resolve eq423185 eq848191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423185 eq848191
  have eq849206 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq849121
  have eq850399 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq849206
  have eq850409 : x = (M.op x y) := by
    first
    | (have r₁ := eq850399
       have r₂ := eq455864
       grind)
    | exact resolve eq850399 eq455864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455864 eq850399
  have eq850885 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq850409 eq20
    | exact resolve eq20 eq850409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq850887 : x ≠ y ∨ y = (k y x) := by
    first
    | exact superpose eq850409 eq50
    | exact resolve eq50 eq850409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq851969 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq850885
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq850885
    | exact resolve eq850885 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850885
  have eq851975 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq851969 eq26
    | exact resolve eq26 eq851969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq852603 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq851975 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq851975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq868669 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq851969 eq99
    | exact resolve eq99 eq851969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq868670 : (σ y) = (M.op (σ x) (σ y)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq868669
       have r₂ := eq27
       grind)
    | exact resolve eq868669 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868669
  have eq868671 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq851969 eq868670
    | exact resolve eq868670 eq851969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868670
  have eq868683 : (k (σ x) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq44
       have i₂ := eq868671
       grind)
    | exact superpose eq868671 eq44
    | exact resolve eq44 eq868671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq868671
  have eq868903 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq868683
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq868683
    | exact resolve eq868683 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868683
  have eq869005 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq851969 eq868903
    | exact resolve eq868903 eq851969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868903
  have eq869225 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq869005 eq515035
    | exact resolve eq515035 eq869005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515035 eq869005
  have eq869268 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = y ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq869225
  have eq1040646 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq869268 eq14
    | (have j0 := eq14 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq14 (σ (M.op x y)) (σ y)
       have r₂ := eq869268
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq869268
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq869268
       grind)
    | exact resolve eq14 eq869268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869268
  have eq1040647 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1040646
  have eq1143306 : (τ (σ (M.op x y))) = (k (M.op x y) y) ∨ x = y ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1040647 eq143
    | exact resolve eq143 eq1040647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq1040647
  have eq1143466 : (τ (σ (M.op x y))) = (k x y) ∨ x = y ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq850409 eq1143306
    | exact resolve eq1143306 eq850409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143306
  have eq1143513 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq1143466
    | exact resolve eq1143466 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1143466
  have eq1143523 : x = (k x y) ∨ x = y ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq850409 eq1143513
    | exact resolve eq1143513 eq850409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143513
  have eq1143526 : x = (k x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq1143523
       have r₂ := eq14 x y
       grind)
    | (have r₁ := eq1143523
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq1143523 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143523
  have eq1143602 : x = y ∨ x = (M.op y x) ∨ x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq456053
       have i₂ := eq1143526
       grind)
    | exact superpose eq1143526 eq456053
    | exact resolve eq456053 eq1143526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456053
  have eq1143616 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3538 x
       have i₂ := eq1143526
       grind)
    | exact superpose eq1143526 eq3538
    | (have j0 := eq3538 x
       grind)
    | exact resolve eq3538 eq1143526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538 eq1143526
  have eq1143668 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1143616
  have eq1143673 : x = (M.op y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1143602
  have eq1143715 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1143668
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1143668
    | exact resolve eq1143668 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143668
  have eq1143828 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1143715
    | exact resolve eq1143715 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143715
  have eq1143829 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq1143828
  have eq1143939 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1143829
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1143829
    | exact resolve eq1143829 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143829
  have eq1144033 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq1143939
    | exact resolve eq1143939 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143939
  have eq1144065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq851969 eq1144033
    | exact resolve eq1144033 eq851969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144033
  have eq1144097 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq1144065
       have r₂ := eq27
       grind)
    | exact resolve eq1144065 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144065
  have eq1144123 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1144097
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1144097
    | exact resolve eq1144097 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144097
  have eq1144149 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq851969 eq1144123
    | exact resolve eq1144123 eq851969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144123
  have eq1144211 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1143673
       grind)
    | exact superpose eq1143673 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1143673
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1143673
       grind)
    | exact resolve eq13 eq1143673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143673
  have eq1144214 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1144211
  have eq1144216 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1144214
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1144214
    | exact resolve eq1144214 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144214
  have eq1144217 : x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq850409 eq1144216
    | exact resolve eq1144216 eq850409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144216
  have eq1144218 : x = y ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1144217
  have eq1144219 : (M.op x y) = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1144218
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1144218
    | exact resolve eq1144218 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144218
  have eq1144220 : x = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq850409 eq1144219
    | exact resolve eq1144219 eq850409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144219
  have eq1144493 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1144149 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ y) (σ (M.op x y))
       have r₂ := eq1144149
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1144149
       grind)
    | exact resolve eq13 eq1144149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144149
  have eq1144496 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1144493
  have eq1144498 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq851975 eq1144496
    | exact resolve eq1144496 eq851975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144496
  have eq1144499 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by grind
  clear eq1144498
  have eq1144500 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq851975 eq1144499
    | exact resolve eq1144499 eq851975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144499
  have eq1144510 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq1144220
       grind)
    | exact superpose eq1144220 eq71
    | exact resolve eq71 eq1144220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144220
  have eq1144974 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq851969 eq1144510
    | exact resolve eq1144510 eq851969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144510
  have eq1145074 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1144974
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1144974
    | exact resolve eq1144974 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144974
  have eq1145163 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq851969 eq1145074
    | exact resolve eq1145074 eq851969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145074
  have eq1145427 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1145163 eq1144500
    | exact resolve eq1144500 eq1145163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144500 eq1145163
  have eq1145460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1145427
  have eq1145475 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq1145460
       have r₂ := eq27
       grind)
    | exact resolve eq1145460 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145460
  have eq1145593 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1145475 eq852603
    | (have r₁ := eq852603
       have r₂ := eq1145475
       grind)
    | exact resolve eq852603 eq1145475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852603 eq1145475
  have eq1145594 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq1145593
  have eq1145621 : (τ (σ y)) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1145594 eq114
    | exact resolve eq114 eq1145594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1145594
  have eq1145776 : (τ (σ y)) = (k y x) ∨ x = y := by
    first
    | exact superpose eq850409 eq1145621
    | exact resolve eq1145621 eq850409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145621
  have eq1145810 : y = (k y x) ∨ x = y := by
    first
    | exact superpose eq29 eq1145776
    | exact resolve eq1145776 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1145776
  have eq1145814 : y = (k y x) := by
    first
    | (have r₁ := eq1145810
       have r₂ := eq850887
       grind)
    | exact resolve eq1145810 eq850887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850887 eq1145810
  have eq1145824 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq1145814
       grind)
    | exact superpose eq1145814 eq71
    | exact resolve eq71 eq1145814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1145949 : (σ y) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq3382 y
       have i₂ := eq1145814
       grind)
    | exact superpose eq1145814 eq3382
    | (have j0 := eq3382 y
       grind)
    | exact resolve eq3382 eq1145814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382
  have eq1145950 : (σ y) ≠ (σ y) ∨ (σ y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq3384 y
       have i₂ := eq1145814
       grind)
    | exact superpose eq1145814 eq3384
    | (have j0 := eq3384 y
       grind)
    | exact resolve eq3384 eq1145814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3384
  have eq1145972 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq1145814
       grind)
    | exact superpose eq1145814 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1145814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1145990 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq1145972
  have eq1145994 : (σ y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1145950
  have eq1145995 : (σ y) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1145949
  have eq1146019 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1145990
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1145990
    | exact resolve eq1145990 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145990
  have eq1146040 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq851969 eq1145994
    | exact resolve eq1145994 eq851969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145994
  have eq1146041 : (σ y) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq851969 eq1145995
    | exact resolve eq1145995 eq851969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145995
  have eq1146119 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq851969 eq1145824
    | exact resolve eq1145824 eq851969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145824
  have eq1146132 : y = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq850409 eq1146019
    | exact resolve eq1146019 eq850409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146019
  have eq1146150 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1146040
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1146040
    | exact resolve eq1146040 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146040
  have eq1146151 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1146041
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1146041
    | exact resolve eq1146041 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146041
  have eq1146224 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1146119
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1146119
    | exact resolve eq1146119 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146119
  have eq1146253 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1146150
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1146150
    | exact resolve eq1146150 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146150
  have eq1146254 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1146151
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1146151
    | exact resolve eq1146151 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146151
  have eq1146313 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1146253
    | exact resolve eq1146253 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146253
  have eq1146314 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1146254
    | exact resolve eq1146254 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1146254
  have eq1146343 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq851969 eq1146313
    | exact resolve eq1146313 eq851969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146313
  have eq1146344 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq851969 eq1146314
    | exact resolve eq1146314 eq851969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146314
  have eq1146373 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1146343
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1146343
    | exact resolve eq1146343 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146343
  have eq1146374 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq1146344
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1146344
    | exact resolve eq1146344 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146344
  have eq1150701 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1146373 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ y) (σ (M.op x y))
       have r₂ := eq1146373
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1146373
       grind)
    | exact resolve eq13 eq1146373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146373
  have eq1150704 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1150701
  have eq1150705 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq851975 eq1150704
    | exact resolve eq1150704 eq851975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150704
  have eq1150706 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1150705
  have eq1150707 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq851975 eq1150706
    | exact resolve eq1150706 eq851975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150706
  have eq1150708 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1146224 eq1150707
    | exact resolve eq1150707 eq1146224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150707
  have eq1150709 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1150708
  have eq1150731 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1146374
       have r₂ := eq1150709
       grind)
    | exact resolve eq1146374 eq1150709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146374
  have eq1150741 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1150731 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1150731
       grind)
    | exact resolve eq13 eq1150731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150731
  have eq1150751 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1150741
       have r₂ := eq1150709
       grind)
    | exact resolve eq1150741 eq1150709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150709 eq1150741
  have eq1150753 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq851975 eq1150751
    | exact resolve eq1150751 eq851975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150751
  have eq1150754 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq1150753
  have eq1150755 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq851975 eq1150754
    | exact resolve eq1150754 eq851975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851975 eq1150754
  have eq1150756 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1146224 eq1150755
    | exact resolve eq1150755 eq1146224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146224 eq1150755
  have eq1150757 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1150756
  have eq1150760 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1150757 eq27
    | exact resolve eq27 eq1150757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1150757
  have eq1163107 : y ≠ y ∨ x = y ∨ y = (M.op x y) ∨ x = (k y x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1146132
       grind)
    | exact superpose eq1146132 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1146132
       grind)
    | exact resolve eq12 eq1146132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146132
  have eq1163111 : y ≠ y ∨ x = y ∨ y = (M.op x y) ∨ x = (k y x) ∨ x = (M.op y x) := by grind
  clear eq1163107
  have eq1163112 : x = y ∨ y = (M.op x y) ∨ x = (k y x) ∨ x = (M.op y x) := by grind
  clear eq1163111
  have eq1163118 : y = (M.op x y) ∨ x = y ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1163112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1163112
    | exact resolve eq1163112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163112
  have eq1163119 : x = y ∨ x = y ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq850409 eq1163118
    | exact resolve eq1163118 eq850409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163118
  have eq1163120 : x = y ∨ x = (k y x) ∨ x = (M.op y x) := by grind
  clear eq1163119
  have eq1163121 : x = y ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1163120
       have i₂ := eq1145814
       grind)
    | exact superpose eq1145814 eq1163120
    | exact resolve eq1163120 eq1145814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163120
  have eq1163122 : x = (M.op y x) ∨ x = y := by grind
  clear eq1163121
  have eq1163125 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1163122
       grind)
    | exact superpose eq1163122 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1163122
       grind)
    | exact resolve eq13 eq1163122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163122
  have eq1163128 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq1163125
  have eq1163131 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq1163128
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1163128
    | exact resolve eq1163128 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163128
  have eq1163132 : x = y ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | exact superpose eq850409 eq1163131
    | exact resolve eq1163131 eq850409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163131
  have eq1163133 : x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq1163132
  have eq1163134 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1163133
       have i₂ := eq1145814
       grind)
    | exact superpose eq1145814 eq1163133
    | exact resolve eq1163133 eq1145814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145814 eq1163133
  have eq1163135 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1163134
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1163134
    | exact resolve eq1163134 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1163134
  have eq1163136 : x = y ∨ x = y := by
    first
    | exact superpose eq850409 eq1163135
    | exact resolve eq1163135 eq850409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850409 eq1163135
  have eq1163137 : x = y := by grind
  clear eq1163136
  have eq1163139 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1163137
       grind)
    | exact superpose eq1163137 eq24
    | exact resolve eq24 eq1163137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1163137
  have eq1164527 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1163139
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1163139
    | exact resolve eq1163139 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1163139
  have eq1165008 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq851969 eq1164527
    | exact resolve eq1164527 eq851969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851969 eq1164527
  have eq1165343 : False := by grind
  exact eq1165343

/-- `x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then m(X,Y) else if m(Y,X) = Y then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyx_x_pxy_y_pyx_y_pxy_pxy_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq70 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq61 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq61
    | (have j0 := eq61 x y
       grind)
    | exact resolve eq61 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq61
    | (have j0 := eq61 (σ x) (σ y)
       grind)
    | exact resolve eq61 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq68
       grind)
    | exact superpose eq68 eq16
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ y = (k y x) := by
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
  have eq79 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq92 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq68
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq68 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq97
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq117 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq132 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq146 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq205 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq613 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq3511 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq146 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq146
    | (have j0 := eq146 x
       grind)
    | exact resolve eq146 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3518 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq146 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq3520 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3511
  have eq3526 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3520
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3520
    | exact resolve eq3520 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq3520
  have eq3545 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | (have r₁ := eq3526
       have r₂ := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq3526 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526
  have eq3552 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3545 eq49
    | exact resolve eq49 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3854 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq205
    | (have j0 := eq205 (M.op x y)
       grind)
    | exact resolve eq205 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq3861 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3854
  have eq3865 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq133 eq3861
    | exact resolve eq3861 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq3861
  have eq3898 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq14 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq3865
       have r₂ := eq14 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3865 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3865
  have eq4069 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (σ (k x X0)) ∨ (σ x) = (k (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq92 eq12
    | (have j0 := eq12 (σ x) (σ X0)
       have j1 := eq92 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq92 x
       grind)
    | (have r₁ := eq12 (σ x) (σ X0)
       have r₂ := eq92 X0
       grind)
    | exact resolve eq12 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq4074 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (σ (k x X0)) ∨ (σ x) = (k (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq4069 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4069
  have eq4078 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (σ (k x X0)) ∨ (σ x) = (k (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq4074 X0
       have j1 := eq12 (σ x) (σ X0)
       grind)
    | (have r₁ := eq4074 x
       have r₂ := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq4074 X0
       have r₂ := eq12 (σ x) (σ X0)
       grind)
    | exact resolve eq4074 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4074
  have eq4116 : ∀ X0 : G, (σ x) = (σ (k x X0)) ∨ (σ X0) ≠ (σ (k x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (σ (k x X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq4078
    | (have j0 := eq4078 X0
       grind)
    | exact resolve eq4078 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4078
  have eq4117 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ x) = (σ (k x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq4116 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4116
  have eq4279 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq93 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq10810 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3545 eq109
    | exact resolve eq109 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq14184 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq10810
       grind)
    | exact superpose eq10810 eq16
    | exact resolve eq16 eq10810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10810
  have eq14235 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3552 eq14184
    | exact resolve eq14184 eq3552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14184
  have eq14238 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq14 x x
       grind)
    | (have r₁ := eq14235
       have r₂ := eq14 x x
       grind)
    | exact resolve eq14235 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14235
  have eq22047 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq22047
    | exact resolve eq22047 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22047
  have eq22059 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq22048
       have r₂ := eq27
       grind)
    | exact resolve eq22048 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22048
  have eq22063 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq22059
    | exact resolve eq22059 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22059
  have eq22065 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq22063
    | exact resolve eq22063 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22063
  have eq22067 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22065 eq61
    | (have r₁ := eq61 (σ y) (σ x)
       have r₂ := eq22065
       grind)
    | (have r₁ := eq61 (σ x) (σ y)
       have r₂ := eq22065
       grind)
    | (have r₁ := eq61 x y
       have r₂ := eq22065
       grind)
    | exact resolve eq61 eq22065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22065
  have eq22070 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq22067
  have eq22147 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22070 eq77
    | exact resolve eq77 eq22070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22070
  have eq22177 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq22147
    | exact resolve eq22147 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22147
  have eq42447 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq22177
       grind)
    | exact superpose eq22177 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq22177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22177
  have eq42448 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq42447
  have eq42452 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42448
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42448
    | exact resolve eq42448 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42448
  have eq42453 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq42452
  have eq42469 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42453
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42453
    | exact resolve eq42453 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42453
  have eq42470 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq42469
  have eq42817 : x ≠ x ∨ x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61 y x
       have i₂ := eq42470
       grind)
    | exact superpose eq42470 eq61
    | (have r₁ := eq61 y x
       have r₂ := eq42470
       grind)
    | (have r₁ := eq61 x y
       have r₂ := eq42470
       grind)
    | (have r₁ := eq61 (σ x) (σ y)
       have r₂ := eq42470
       grind)
    | exact resolve eq61 eq42470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42818 : x ≠ x ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq42470
       grind)
    | exact superpose eq42470 eq14
    | (have j0 := eq14 x y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq42470
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq42470
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq42470
       grind)
    | exact resolve eq14 eq42470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42470
  have eq42819 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq42818
  have eq42820 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq42817
  have eq42821 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq42819
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42819
    | exact resolve eq42819 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42819
  have eq42822 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq42821
       have r₂ := eq71
       grind)
    | exact resolve eq42821 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42821
  have eq42827 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq42822
       grind)
    | exact superpose eq42822 eq44
    | exact resolve eq44 eq42822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42822
  have eq42879 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq42827
    | exact resolve eq42827 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42827
  have eq43339 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq613 x y
       have i₂ := eq42820
       grind)
    | exact superpose eq42820 eq613
    | (have j0 := eq613 x y
       grind)
    | exact resolve eq613 eq42820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq42820
  have eq43345 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq43339
  have eq43349 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43345
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43345
    | exact resolve eq43345 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43345
  have eq43362 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43349
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43349
    | exact resolve eq43349 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43349
  have eq43368 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43362
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43362
    | exact resolve eq43362 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43362
  have eq43372 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43368
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43368
    | exact resolve eq43368 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43368
  have eq43376 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq43372
    | exact resolve eq43372 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43372
  have eq43377 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq43376
  have eq43381 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43377
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43377
    | exact resolve eq43377 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43377
  have eq43387 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43381
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43381
    | exact resolve eq43381 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43381
  have eq43390 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq43387
    | exact resolve eq43387 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43387
  have eq43391 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq43390
  have eq43786 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43391 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq43391
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq43391
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq43391
       grind)
    | exact resolve eq14 eq43391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43391
  have eq43787 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq43786
  have eq43790 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq43787
    | exact resolve eq43787 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43787
  have eq43791 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq43790
       have r₂ := eq72
       grind)
    | exact resolve eq43790 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43790
  have eq43819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43791 eq42879
    | exact resolve eq42879 eq43791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42879 eq43791
  have eq43826 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq43819
  have eq43845 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq43826
       have r₂ := eq27
       grind)
    | exact resolve eq43826 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43826
  have eq44182 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43845 eq72
    | (have r₁ := eq72
       have r₂ := eq43845
       grind)
    | exact resolve eq72 eq43845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43845
  have eq44230 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq44182
  have eq44588 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44230 eq55
    | exact resolve eq55 eq44230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44230
  have eq44660 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq44588
    | exact resolve eq44588 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44588
  have eq44699 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq44660
       grind)
    | exact superpose eq44660 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq44660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44700 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq44699
  have eq44721 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44700
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq44700
    | exact resolve eq44700 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44700
  have eq44722 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq44721
  have eq65617 : y ≠ y ∨ y = (M.op x y) ∨ x = y ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq44722
       grind)
    | exact superpose eq44722 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq44722
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq44722
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq44722
       grind)
    | exact resolve eq12 eq44722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65620 : x ≠ y ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq44722
  have eq65621 : y = (M.op x y) ∨ x = y ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq65617
  have eq65626 : y = (M.op x y) ∨ x = y ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65621
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq65621
    | exact resolve eq65621 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65621
  have eq65627 : y = (M.op x y) ∨ x = y ∨ x = (k x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq65626
  have eq670812 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq65627
       have r₂ := eq65620
       grind)
    | exact resolve eq65627 eq65620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65627
  have eq670872 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44660
       have i₂ := eq670812
       grind)
    | exact superpose eq670812 eq44660
    | exact resolve eq44660 eq670812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670812
  have eq671201 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq670872
  have eq671269 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq671201
       have r₂ := eq65620
       grind)
    | exact resolve eq671201 eq65620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65620 eq671201
  have eq671348 : x ≠ x ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq671269
       grind)
    | exact superpose eq671269 eq14
    | (have j0 := eq14 x y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq671269
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq671269
       grind)
    | exact resolve eq14 eq671269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671269
  have eq671351 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq671348
  have eq671353 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq671351
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq671351
    | exact resolve eq671351 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671351
  have eq671354 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq671353
       have r₂ := eq71
       grind)
    | exact resolve eq671353 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671353
  have eq671401 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44660
       have i₂ := eq671354
       grind)
    | exact superpose eq671354 eq44660
    | exact resolve eq44660 eq671354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44660 eq671354
  have eq671621 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq671401
  have eq671830 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq671621 eq27
    | exact resolve eq27 eq671621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671832 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq671621 eq72
    | exact resolve eq72 eq671621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671833 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq671621 eq79
    | (have r₁ := eq79
       have r₂ := eq671621
       grind)
    | exact resolve eq79 eq671621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq671621
  have eq671834 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq671833
  have eq715712 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq671834 eq77
    | exact resolve eq77 eq671834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq715839 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq715712
    | exact resolve eq715712 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715712
  have eq744582 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq715839 eq61
    | (have r₁ := eq61 (σ y) (σ x)
       have r₂ := eq715839
       grind)
    | (have r₁ := eq61 x y
       have r₂ := eq715839
       grind)
    | exact resolve eq61 eq715839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715839
  have eq744583 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq744582
  have eq762950 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq744583 eq118
    | exact resolve eq118 eq744583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq744583
  have eq763052 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (k y x) := by grind
  clear eq762950
  have eq763065 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have r₁ := eq763052
       have r₂ := eq671830
       grind)
    | exact resolve eq763052 eq671830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671830 eq763052
  have eq763072 : y = (k y x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq763065
       have r₂ := eq78
       grind)
    | exact resolve eq763065 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763065
  have eq763112 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq763072
       grind)
    | exact superpose eq763072 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq763072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763072
  have eq763125 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq763112
  have eq763148 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq763125
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq763125
    | exact resolve eq763125 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763125
  have eq763149 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq763148
  have eq763189 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq763149
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq763149
    | exact resolve eq763149 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763149
  have eq763257 : x ≠ x ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq763189
       grind)
    | exact superpose eq763189 eq14
    | (have j0 := eq14 x y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq763189
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq763189
       grind)
    | exact resolve eq14 eq763189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763258 : x ≠ x ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61 y x
       have i₂ := eq763189
       grind)
    | exact superpose eq763189 eq61
    | (have r₁ := eq61 y x
       have r₂ := eq763189
       grind)
    | (have r₁ := eq61 x y
       have r₂ := eq763189
       grind)
    | exact resolve eq61 eq763189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763189
  have eq763259 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq763258
  have eq763260 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq763257
  have eq763262 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq763260
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq763260
    | exact resolve eq763260 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763260
  have eq763263 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq763262
       have r₂ := eq71
       grind)
    | exact resolve eq763262 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763262
  have eq763271 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq763263
       grind)
    | exact superpose eq763263 eq44
    | exact resolve eq44 eq763263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763263
  have eq763630 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq763271
    | exact resolve eq763271 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763271
  have eq764208 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq763259
       grind)
    | exact superpose eq763259 eq68
    | exact resolve eq68 eq763259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq763259
  have eq764305 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq764208
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq764208
    | exact resolve eq764208 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764208
  have eq764438 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq764305 eq671834
    | exact resolve eq671834 eq764305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671834 eq764305
  have eq764461 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq764438
  have eq764562 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq764461 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq764461
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq764461
       grind)
    | exact resolve eq14 eq764461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764461
  have eq764565 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq764562
  have eq764605 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq764565
    | exact resolve eq764565 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764565
  have eq764876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq764605 eq763630
    | exact resolve eq763630 eq764605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763630 eq764605
  have eq764891 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq764876
  have eq765143 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq764891
       have r₂ := eq27
       grind)
    | exact resolve eq764891 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764891
  have eq765149 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k y X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq765143 eq36
    | exact resolve eq36 eq765143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq765150 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq765143 eq40
    | exact resolve eq40 eq765143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq765153 : (k x y) = (τ (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq765143 eq55
    | exact resolve eq55 eq765143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq765865 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq765143 eq671832
    | (have r₁ := eq671832
       have r₂ := eq765143
       grind)
    | exact resolve eq671832 eq765143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671832 eq765143
  have eq765980 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq765865
  have eq765981 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq765980
  have eq766586 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3545 eq765981
    | exact resolve eq765981 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3545 eq765981
  have eq766663 : (k x x) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49 eq765153
    | exact resolve eq765153 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq765153
  have eq766666 : ∀ X0 : G, (σ (k X0 x)) = (σ (k X0 y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq39 eq765150
    | exact resolve eq765150 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq765150
  have eq766667 : ∀ X0 : G, (σ (k x X0)) = (σ (k y X0)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq35 eq765149
    | exact resolve eq765149 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq765149
  have eq766702 : (k x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq766663
       have i₂ := eq14238
       grind)
    | exact superpose eq14238 eq766663
    | exact resolve eq766663 eq14238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766663
  have eq769042 : (τ (σ x)) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq766586 eq3552
    | exact resolve eq3552 eq766586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3552 eq766586
  have eq769076 : (τ (σ x)) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq769042
       have i₂ := eq14238
       grind)
    | exact superpose eq14238 eq769042
    | exact resolve eq769042 eq14238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14238 eq769042
  have eq769085 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq769076
    | exact resolve eq769076 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769076
  have eq801253 : ∀ X0 : G, (k X0 y) = (τ (σ (k X0 x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 y)
       have i₂ := eq766666 X0
       grind)
    | exact superpose eq766666 eq16
    | exact resolve eq16 eq766666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766666
  have eq801778 : ∀ X0 : G, (k X0 x) = (k X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq801253 X0
       have i₂ := eq16 (k X0 x)
       grind)
    | exact superpose eq16 eq801253
    | exact resolve eq801253 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801253
  have eq809645 : ∀ X0 : G, (k y X0) = (τ (σ (k x X0))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 (k y X0)
       have i₂ := eq766667 X0
       grind)
    | exact superpose eq766667 eq16
    | exact resolve eq16 eq766667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766667
  have eq810164 : ∀ X0 : G, (k x X0) = (k y X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq809645 X0
       have i₂ := eq16 (k x X0)
       grind)
    | exact superpose eq16 eq809645
    | exact resolve eq809645 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809645
  have eq811668 : (k x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq801778 y
       have i₂ := eq810164 y
       grind)
    | exact superpose eq810164 eq801778
    | exact resolve eq801778 eq810164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801778 eq810164
  have eq811742 : (k x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq811668
  have eq817712 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq811742
       grind)
    | exact superpose eq811742 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq811742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811742
  have eq817753 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq817712
       have r₂ := eq14 x y
       grind)
    | (have r₁ := eq817712
       have r₂ := eq14 y x
       grind)
    | exact resolve eq817712 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817712
  have eq817808 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq61 x y
       grind)
    | (have r₁ := eq817753
       have r₂ := eq61 x y
       grind)
    | exact resolve eq817753 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817753
  have eq817836 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq817808
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq817808
    | exact resolve eq817808 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817808
  have eq817865 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq817836
       have r₂ := eq71
       grind)
    | exact resolve eq817836 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817836
  have eq817895 : x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq817865
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq817865
    | exact resolve eq817865 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817865
  have eq817896 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq817895
  have eq817948 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq817896
       grind)
    | exact superpose eq817896 eq44
    | exact resolve eq44 eq817896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq818112 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq766702
       have i₂ := eq817896
       grind)
    | exact superpose eq817896 eq766702
    | exact resolve eq766702 eq817896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766702 eq817896
  have eq818148 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq818112
  have eq818351 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq817948
    | exact resolve eq817948 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817948
  have eq819046 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq769085
       have i₂ := eq818148
       grind)
    | exact superpose eq818148 eq769085
    | exact resolve eq769085 eq818148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769085 eq818148
  have eq819061 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq819046
  have eq819098 : y ≠ y ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq819061 eq71
    | (have r₁ := eq71
       have r₂ := eq819061
       grind)
    | exact resolve eq71 eq819061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq819380 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq819061
  have eq819389 : y = (k x y) ∨ x = (M.op x y) := by grind
  clear eq819098
  have eq821683 : (σ y) ≠ (σ y) ∨ (σ y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4117 y
       have i₂ := eq819389
       grind)
    | exact superpose eq819389 eq4117
    | (have j0 := eq4117 y
       grind)
    | exact resolve eq4117 eq819389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4117 eq819389
  have eq821706 : (σ y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq821683
  have eq821974 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq821706
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq821706
    | exact resolve eq821706 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821706
  have eq822037 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq821974
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq821974
    | exact resolve eq821974 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821974
  have eq822069 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq822037
    | exact resolve eq822037 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822037
  have eq822091 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq822069
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq822069
    | exact resolve eq822069 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822069
  have eq1021029 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq822091 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq822091
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq822091
       grind)
    | exact resolve eq14 eq822091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822091
  have eq1021032 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1021029
  have eq1021074 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1021032
    | exact resolve eq1021032 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021032
  have eq1021077 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1021074
       have r₂ := eq72
       grind)
    | exact resolve eq1021074 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1021074
  have eq1021774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1021077 eq818351
    | exact resolve eq818351 eq1021077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818351 eq1021077
  have eq1021885 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1021774
  have eq1022173 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1021885
       have r₂ := eq27
       grind)
    | exact resolve eq1021885 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021885
  have eq1022204 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1022173 eq29
    | exact resolve eq29 eq1022173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022173
  have eq1024246 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq1022204
    | exact resolve eq1022204 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1022204
  have eq1024288 : x = (M.op x y) := by
    first
    | (have r₁ := eq1024246
       have r₂ := eq819380
       grind)
    | exact resolve eq1024246 eq819380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819380 eq1024246
  have eq1024325 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1024288 eq20
    | exact resolve eq20 eq1024288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1024331 : x ≠ y ∨ x = (k x y) := by
    first
    | exact superpose eq1024288 eq71
    | exact resolve eq71 eq1024288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1024332 : x ≠ x ∨ x = (M.op y x) ∨ x = y ∨ y = (k y x) := by
    first
    | exact superpose eq1024288 eq78
    | (have r₁ := eq78
       have r₂ := eq1024288
       grind)
    | exact resolve eq78 eq1024288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1024713 : y = (k y x) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq1024332
  have eq1025066 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1024325
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1024325
    | exact resolve eq1024325 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024325
  have eq1025120 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1025066 eq26
    | exact resolve eq26 eq1025066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1026164 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1025120 eq61
    | (have j0 := eq61 (σ x) (σ y)
       grind)
    | exact resolve eq61 eq1025120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1033481 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq3518 y
       have i₂ := eq1024713
       grind)
    | exact superpose eq1024713 eq3518
    | (have j0 := eq3518 y
       grind)
    | exact resolve eq3518 eq1024713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3518
  have eq1033513 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq1033481
  have eq1033550 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq1025066 eq1033513
    | exact resolve eq1033513 eq1025066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033513
  have eq1033630 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1033550
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1033550
    | exact resolve eq1033550 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033550
  have eq1033708 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1033630
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1033630
    | exact resolve eq1033630 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033630
  have eq1033763 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq1033708
    | exact resolve eq1033708 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033708
  have eq1033785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq1025066 eq1033763
    | exact resolve eq1033763 eq1025066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033763
  have eq1033802 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1033785
       have r₂ := eq27
       grind)
    | exact resolve eq1033785 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033785
  have eq1033815 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1033802
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1033802
    | exact resolve eq1033802 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033802
  have eq1033827 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq1033815
    | exact resolve eq1033815 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033815
  have eq1394127 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq1033827 eq61
    | (have r₁ := eq61 (σ y) (σ (M.op x y))
       have r₂ := eq1033827
       grind)
    | (have r₁ := eq61 (σ x) (σ y)
       have r₂ := eq1033827
       grind)
    | (have r₁ := eq61 y x
       have r₂ := eq1033827
       grind)
    | exact resolve eq61 eq1033827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033827
  have eq1394128 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq1394127
  have eq1437840 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq1394128 eq89
    | exact resolve eq89 eq1394128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq1394128
  have eq1438010 : (τ (σ (M.op x y))) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq1024288 eq1437840
    | exact resolve eq1437840 eq1024288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437840
  have eq1438054 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq1438010
    | exact resolve eq1438010 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1438010
  have eq1438079 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq1024288 eq1438054
    | exact resolve eq1438054 eq1024288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438054
  have eq1438166 : x = y ∨ x = y ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1024713
       have i₂ := eq1438079
       grind)
    | exact superpose eq1438079 eq1024713
    | exact resolve eq1024713 eq1438079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024713 eq1438079
  have eq1438224 : x = (M.op y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1438166
  have eq1438618 : x ≠ x ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq1438224
       grind)
    | exact superpose eq1438224 eq14
    | (have j0 := eq14 x y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq1438224
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq1438224
       grind)
    | exact resolve eq14 eq1438224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1438619 : x ≠ x ∨ x = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61 y x
       have i₂ := eq1438224
       grind)
    | exact superpose eq1438224 eq61
    | (have r₁ := eq61 y x
       have r₂ := eq1438224
       grind)
    | (have r₁ := eq61 (σ x) (σ y)
       have r₂ := eq1438224
       grind)
    | exact resolve eq61 eq1438224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1438224
  have eq1438620 : x = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1438619
  have eq1438621 : (M.op x y) = (k x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1438618
  have eq1438624 : (M.op x y) = (k x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1438621
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1438621
    | exact resolve eq1438621 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438621
  have eq1438625 : x = (k x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1024288 eq1438624
    | exact resolve eq1438624 eq1024288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438624
  have eq1438626 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1438625
       have r₂ := eq1024331
       grind)
    | exact resolve eq1438625 eq1024331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438625
  have eq1438647 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1438626
       grind)
    | exact superpose eq1438626 eq44
    | exact resolve eq44 eq1438626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438626
  have eq1439268 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1025066 eq1438647
    | exact resolve eq1438647 eq1025066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438647
  have eq1439363 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1439268
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1439268
    | exact resolve eq1439268 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439268
  have eq1439449 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1025066 eq1439363
    | exact resolve eq1439363 eq1025066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439363
  have eq1439990 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4279 x
       have i₂ := eq1438620
       grind)
    | exact superpose eq1438620 eq4279
    | (have j0 := eq4279 x
       grind)
    | exact resolve eq4279 eq1438620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4279 eq1438620
  have eq1440019 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1439990
  have eq1440045 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1440019
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1440019
    | exact resolve eq1440019 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440019
  have eq1440135 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1025066 eq1440045
    | exact resolve eq1440045 eq1025066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440045
  have eq1440222 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1440135
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1440135
    | exact resolve eq1440135 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440135
  have eq1440300 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1440222
    | exact resolve eq1440222 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440222
  have eq1440349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1025066 eq1440300
    | exact resolve eq1440300 eq1025066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440300
  have eq1440370 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1440349
       have r₂ := eq27
       grind)
    | exact resolve eq1440349 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440349
  have eq1440389 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1440370
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1440370
    | exact resolve eq1440370 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440370
  have eq1440407 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1440389
    | exact resolve eq1440389 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1440389
  have eq1440408 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1440407
  have eq1440783 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1440408 eq14
    | (have j0 := eq14 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq14 (σ (M.op x y)) (σ y)
       have r₂ := eq1440408
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq1440408
       grind)
    | exact resolve eq14 eq1440408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440408
  have eq1440786 : (M.op (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1440783
  have eq1440795 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1025120 eq1440786
    | exact resolve eq1440786 eq1025120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440786
  have eq1440796 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq1440795
       have r₂ := eq1026164
       grind)
    | exact resolve eq1440795 eq1026164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440795
  have eq1440888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1440796 eq1439449
    | exact resolve eq1439449 eq1440796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439449 eq1440796
  have eq1440924 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq1440888
       have r₂ := eq27
       grind)
    | exact resolve eq1440888 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440888
  have eq1441454 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1440924 eq1026164
    | (have r₁ := eq1026164
       have r₂ := eq1440924
       grind)
    | exact resolve eq1026164 eq1440924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026164 eq1440924
  have eq1441495 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by grind
  clear eq1441454
  have eq1441538 : (τ (σ y)) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq1441495 eq159
    | exact resolve eq159 eq1441495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq1441495
  have eq1441721 : (τ (σ y)) = (k x y) ∨ x = y := by
    first
    | exact superpose eq1024288 eq1441538
    | exact resolve eq1441538 eq1024288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441538
  have eq1441764 : y = (k x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1441721
    | exact resolve eq1441721 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1441721
  have eq1442180 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq1441764
       grind)
    | exact superpose eq1441764 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1441764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1442195 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq1442180
  have eq1442225 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1442195
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1442195
    | exact resolve eq1442195 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442195
  have eq1442326 : x = y ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1024288 eq1442225
    | exact resolve eq1442225 eq1024288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442225
  have eq1442327 : y = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by grind
  clear eq1442326
  have eq1484204 : y ≠ y ∨ y = (M.op x y) ∨ x = y ∨ x = (k x y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1442327
       grind)
    | exact superpose eq1442327 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1442327
       grind)
    | exact resolve eq12 eq1442327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442327
  have eq1484208 : y ≠ y ∨ y = (M.op x y) ∨ x = y ∨ x = (k x y) ∨ x = (M.op y x) := by grind
  clear eq1484204
  have eq1484209 : y = (M.op x y) ∨ x = y ∨ x = (k x y) ∨ x = (M.op y x) := by grind
  clear eq1484208
  have eq1484217 : y = (M.op x y) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1484209
       have r₂ := eq1024331
       grind)
    | exact resolve eq1484209 eq1024331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484209
  have eq1484218 : y = (M.op x y) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1484217
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1484217
    | exact resolve eq1484217 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484217
  have eq1484219 : x = y ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1024288 eq1484218
    | exact resolve eq1484218 eq1024288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484218
  have eq1484220 : x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1484219
       have r₂ := eq1024331
       grind)
    | exact resolve eq1484219 eq1024331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484219
  have eq1484639 : x = y ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1441764
       have i₂ := eq1484220
       grind)
    | exact superpose eq1484220 eq1441764
    | exact resolve eq1441764 eq1484220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484220
  have eq1484680 : x = (M.op y x) ∨ x = y := by grind
  clear eq1484639
  have eq1485105 : x ≠ x ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq1484680
       grind)
    | exact superpose eq1484680 eq14
    | (have j0 := eq14 x y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq1484680
       grind)
    | exact resolve eq14 eq1484680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484680
  have eq1485108 : (M.op x y) = (k x y) ∨ x = y := by grind
  clear eq1485105
  have eq1485112 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq1485108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1485108
    | exact resolve eq1485108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1485108
  have eq1485113 : x = (k x y) ∨ x = y := by
    first
    | exact superpose eq1024288 eq1485112
    | exact resolve eq1485112 eq1024288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024288 eq1485112
  have eq1485114 : x = (k x y) := by
    first
    | (have r₁ := eq1485113
       have r₂ := eq1024331
       grind)
    | exact resolve eq1485113 eq1024331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024331 eq1485113
  have eq1485138 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1485114
       grind)
    | exact superpose eq1485114 eq44
    | exact resolve eq44 eq1485114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1485534 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1441764
       have i₂ := eq1485114
       grind)
    | exact superpose eq1485114 eq1441764
    | exact resolve eq1441764 eq1485114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441764 eq1485114
  have eq1485573 : x = y := by grind
  clear eq1485534
  have eq1485699 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1025066 eq1485138
    | exact resolve eq1485138 eq1025066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485138
  have eq1485798 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1485699
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1485699
    | exact resolve eq1485699 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485699
  have eq1485882 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1025066 eq1485798
    | exact resolve eq1485798 eq1025066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485798
  have eq1485994 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1485573
       grind)
    | exact superpose eq1485573 eq24
    | exact resolve eq24 eq1485573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1485573
  have eq1487590 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1485994
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1485994
    | exact resolve eq1485994 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1485994
  have eq1487969 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1025066 eq1487590
    | exact resolve eq1487590 eq1025066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025066 eq1487590
  have eq1489414 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1487969 eq1025120
    | exact resolve eq1025120 eq1487969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025120
  have eq1490253 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1487969 eq1485882
    | exact resolve eq1485882 eq1487969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485882 eq1487969
  have eq1490254 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3898 eq1490253
    | exact resolve eq1490253 eq3898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3898 eq1490253
  have eq1490930 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1490254 eq1489414
    | exact resolve eq1489414 eq1490254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489414 eq1490254
  have eq1490931 : False := by grind
  exact eq1490931
