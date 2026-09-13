import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_pxy_pxy_pyy_pxy_pyy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
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
  clear eq36
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ X0 = X1 := by
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
  have eq61 : (M.op x y) ≠ (k x x) ∨ (k x y) = (k y y) ∨ x = y := by
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
  have eq62 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ x) (σ y)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  clear eq86
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 := by
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
  have eq106 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq130 : (M.op x y) ≠ (k y y) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y := by
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
  have eq131 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq88
    | (have j0 := eq88 (σ x) (σ y)
       grind)
    | exact resolve eq88 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq545 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq74
    | exact resolve eq74 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq21 eq545
    | exact resolve eq545 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq673 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
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
  have eq674 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq673
  have eq675 : (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq674
  have eq709 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq97 eq131
    | (have r₁ := eq131
       have r₂ := eq97
       grind)
    | exact resolve eq131 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq709
  have eq711 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq710
  have eq905 : ∀ X0 : G, (σ (k X0 y)) ≠ (k (σ y) (σ y)) ∨ (k (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq41 eq106
    | (have j0 := eq106 (σ X0) (σ y)
       grind)
    | exact resolve eq106 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq106
  have eq913 : ∀ X0 : G, (σ (k X0 y)) ≠ (k (σ y) (σ y)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq905 X0
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq905
    | (have j0 := eq905 X0
       grind)
    | (have r₁ := eq905 y
       have r₂ := eq10 y y
       grind)
    | exact resolve eq905 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq22685 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq546 eq97
    | exact resolve eq97 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq22721 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq22685
       have r₂ := eq28
       grind)
    | exact resolve eq22685 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22685
  have eq22729 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq22721 eq56
    | exact resolve eq56 eq22721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22721
  have eq22740 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq22729
       have i₂ := eq675
       grind)
    | exact superpose eq675 eq22729
    | exact resolve eq22729 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22729
  have eq22771 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq22740
  have eq23062 : (k (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq22771
       grind)
    | exact superpose eq22771 eq44
    | exact resolve eq44 eq22771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22771
  have eq23145 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq23062
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq23062
    | exact resolve eq23062 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23062
  have eq23146 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq23145
  have eq23184 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq23146 eq62
    | (have r₁ := eq62
       have r₂ := eq23146
       grind)
    | exact resolve eq62 eq23146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23146
  have eq23213 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq23184
  have eq23214 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq23213
  have eq23821 : (τ (k (σ x) (σ y))) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq23214 eq85
    | exact resolve eq85 eq23214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23214
  have eq23865 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq56 eq23821
    | exact resolve eq23821 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23821
  have eq23868 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq23865
       have r₂ := eq61
       grind)
    | exact resolve eq23865 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23865
  have eq23870 : (σ (k x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq23868
       grind)
    | exact superpose eq23868 eq74
    | exact resolve eq74 eq23868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23873 : (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq23868
       grind)
    | exact superpose eq23868 eq96
    | exact resolve eq96 eq23868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq23868
  have eq23906 : (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq23873
  have eq23922 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq23870
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq23870
    | exact resolve eq23870 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23870
  have eq23944 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq23906
       grind)
    | exact superpose eq23906 eq45
    | exact resolve eq45 eq23906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23993 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq23944
    | exact resolve eq23944 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23944
  have eq24272 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23993 eq711
    | exact resolve eq711 eq23993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23993
  have eq24280 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq24272
  have eq24284 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq24280
       have r₂ := eq28
       grind)
    | exact resolve eq24280 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24280
  have eq24301 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq23922 eq97
    | exact resolve eq97 eq23922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq24302 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq23922 eq131
    | exact resolve eq131 eq23922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq23922
  have eq24333 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq24302
  have eq24334 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq24301
  have eq24343 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq24333
       have r₂ := eq711
       grind)
    | exact resolve eq24333 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq24333
  have eq26578 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq24284 eq62
    | (have r₁ := eq62
       have r₂ := eq24284
       grind)
    | exact resolve eq62 eq24284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq24284
  have eq26608 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq26578
  have eq26609 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq26608
  have eq42170 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq24343 eq24334
    | exact resolve eq24334 eq24343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24334 eq24343
  have eq42206 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq42170
  have eq53260 : (τ (k (σ x) (σ y))) = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq26609 eq85
    | exact resolve eq85 eq26609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq26609
  have eq53306 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq56 eq53260
    | exact resolve eq53260 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq53260
  have eq53309 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq53306
       have r₂ := eq61
       grind)
    | exact resolve eq53306 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53306
  have eq53316 : (M.op x y) ≠ (k x y) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq130
       have i₂ := eq53309
       grind)
    | exact superpose eq53309 eq130
    | exact resolve eq130 eq53309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq53309
  have eq53346 : (M.op x y) ≠ (k x y) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq53316
  have eq53360 : (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq53346
       have r₂ := eq675
       grind)
    | exact resolve eq53346 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq53346
  have eq56654 : (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq23906
       have i₂ := eq53360
       grind)
    | exact superpose eq53360 eq23906
    | exact resolve eq23906 eq53360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23906 eq53360
  have eq56708 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by grind
  clear eq56654
  have eq56756 : (τ (σ (M.op x y))) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq56708 eq52
    | exact resolve eq52 eq56708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56708
  have eq56854 : (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq31 eq56756
    | exact resolve eq56756 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq56756
  have eq56855 : (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq56854
  have eq56862 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq56855
       grind)
    | exact superpose eq56855 eq44
    | exact resolve eq44 eq56855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56864 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (k y y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61
       have i₂ := eq56855
       grind)
    | exact superpose eq56855 eq61
    | (have r₁ := eq61
       have r₂ := eq56855
       grind)
    | exact resolve eq61 eq56855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq56855
  have eq56934 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq56864
  have eq56935 : (k x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq56934
  have eq56966 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq56862
    | exact resolve eq56862 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56862
  have eq57001 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq56966 eq42206
    | exact resolve eq42206 eq56966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42206
  have eq57078 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq57001
  have eq57084 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq57078
       have r₂ := eq28
       grind)
    | exact resolve eq57078 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57078
  have eq57100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq57084
       grind)
    | exact superpose eq57084 eq45
    | exact resolve eq45 eq57084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57124 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq913 x
       have i₂ := eq57084
       grind)
    | exact superpose eq57084 eq913
    | (have j0 := eq913 x
       grind)
    | exact resolve eq913 eq57084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913 eq57084
  have eq57137 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq57124
    | exact resolve eq57124 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57124
  have eq57158 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq57100
    | exact resolve eq57100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57100
  have eq57160 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57137
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq57137
    | exact resolve eq57137 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57137
  have eq57162 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57160
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq57160
    | exact resolve eq57160 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq57160
  have eq57164 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq57162
    | exact resolve eq57162 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57162
  have eq57166 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57164
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq57164
    | exact resolve eq57164 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57164
  have eq57167 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq57166
  have eq57169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq57167
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq57167
    | exact resolve eq57167 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57167
  have eq57172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq57169
    | exact resolve eq57169 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57169
  have eq57174 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq57172
    | exact resolve eq57172 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57172
  have eq57176 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq57174
       have r₂ := eq28
       grind)
    | exact resolve eq57174 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57174
  have eq57230 : (σ (k x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq56935
       grind)
    | exact superpose eq56935 eq74
    | exact resolve eq74 eq56935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq56935
  have eq57283 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57230
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq57230
    | exact resolve eq57230 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq57230
  have eq61332 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq57283 eq57176
    | exact resolve eq57176 eq57283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57176 eq57283
  have eq61333 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq61332
  have eq61341 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq61333
       have r₂ := eq57158
       grind)
    | exact resolve eq61333 eq57158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57158 eq61333
  have eq61363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq61341 eq56966
    | exact resolve eq56966 eq61341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56966 eq61341
  have eq61386 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq61363
  have eq61400 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq61386
       have r₂ := eq28
       grind)
    | exact resolve eq61386 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61386
  have eq61403 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq61400 eq30
    | exact resolve eq30 eq61400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq61400
  have eq61524 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq61403
    | exact resolve eq61403 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq61403
  have eq61525 : x = y := by grind
  clear eq61524
  have eq61779 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq61525
       grind)
    | exact superpose eq61525 eq19
    | exact resolve eq19 eq61525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq61780 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq61525
       grind)
    | exact superpose eq61525 eq25
    | exact resolve eq25 eq61525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq61525
  have eq62058 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq61780
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq61780
    | exact resolve eq61780 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq61780
  have eq62059 : (M.op x y) = (k x x) := by grind
  clear eq61779
  have eq62060 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq62058 eq27
    | exact resolve eq27 eq62058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq62058
  have eq62182 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq62060
  have eq62318 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq62182 eq52
    | exact resolve eq52 eq62182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq62182
  have eq62361 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq62318
       have i₂ := eq62059
       grind)
    | exact superpose eq62059 eq62318
    | exact resolve eq62318 eq62059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62059 eq62318
  have eq62376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62361 eq15
    | exact resolve eq15 eq62361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62361
  have eq62601 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq62376
    | exact resolve eq62376 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq62376
  have eq62671 : False := by grind
  exact eq62671

/-- `x □ y = if X = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_pxy_pxy_pyy_pyx_pyy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
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
  clear eq36
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ X0 = X1 := by
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
  have eq61 : (M.op x y) ≠ (k x x) ∨ (k x y) = (k y y) ∨ x = y := by
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
  have eq62 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ x) (σ y)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  clear eq86
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 := by
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
  have eq106 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq130 : (M.op x y) ≠ (k y y) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y := by
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
  have eq131 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq88
    | (have j0 := eq88 (σ x) (σ y)
       grind)
    | exact resolve eq88 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq545 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq74
    | exact resolve eq74 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq21 eq545
    | exact resolve eq545 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq673 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
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
  have eq674 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq673
  have eq675 : (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq674
  have eq709 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq97 eq131
    | (have r₁ := eq131
       have r₂ := eq97
       grind)
    | exact resolve eq131 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq709
  have eq711 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq710
  have eq905 : ∀ X0 : G, (σ (k X0 y)) ≠ (k (σ y) (σ y)) ∨ (k (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq41 eq106
    | (have j0 := eq106 (σ X0) (σ y)
       grind)
    | exact resolve eq106 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq106
  have eq913 : ∀ X0 : G, (σ (k X0 y)) ≠ (k (σ y) (σ y)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq905 X0
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq905
    | (have j0 := eq905 X0
       grind)
    | (have r₁ := eq905 y
       have r₂ := eq10 y y
       grind)
    | exact resolve eq905 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq29271 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq546 eq97
    | exact resolve eq97 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq29306 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq29271
       have r₂ := eq28
       grind)
    | exact resolve eq29271 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29271
  have eq29314 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq29306 eq56
    | exact resolve eq56 eq29306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29306
  have eq29325 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq29314
       have i₂ := eq675
       grind)
    | exact superpose eq675 eq29314
    | exact resolve eq29314 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29314
  have eq29362 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq29325
  have eq29675 : (k (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq29362
       grind)
    | exact superpose eq29362 eq44
    | exact resolve eq44 eq29362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29362
  have eq29769 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq29675
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq29675
    | exact resolve eq29675 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29675
  have eq29770 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq29769
  have eq29814 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq29770 eq62
    | (have r₁ := eq62
       have r₂ := eq29770
       grind)
    | exact resolve eq62 eq29770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29770
  have eq29842 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq29814
  have eq29843 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq29842
  have eq30487 : (τ (k (σ x) (σ y))) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq29843 eq85
    | exact resolve eq85 eq29843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29843
  have eq30530 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq56 eq30487
    | exact resolve eq30487 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30487
  have eq30533 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq30530
       have r₂ := eq61
       grind)
    | exact resolve eq30530 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30530
  have eq30535 : (σ (k x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq30533
       grind)
    | exact superpose eq30533 eq74
    | exact resolve eq74 eq30533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30538 : (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq30533
       grind)
    | exact superpose eq30533 eq96
    | exact resolve eq96 eq30533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq30533
  have eq30582 : (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq30538
  have eq30610 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq30535
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq30535
    | exact resolve eq30535 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30535
  have eq30632 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq30582
       grind)
    | exact superpose eq30582 eq45
    | exact resolve eq45 eq30582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30693 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq30632
    | exact resolve eq30632 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30632
  have eq30982 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30693 eq711
    | exact resolve eq711 eq30693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30693
  have eq30990 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq30982
  have eq30994 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq30990
       have r₂ := eq28
       grind)
    | exact resolve eq30990 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30990
  have eq31011 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq30610 eq97
    | exact resolve eq97 eq30610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq31012 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq30610 eq131
    | exact resolve eq131 eq30610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq30610
  have eq31042 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq31012
  have eq31043 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq31011
  have eq31052 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq31042
       have r₂ := eq711
       grind)
    | exact resolve eq31042 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq31042
  have eq33367 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq30994 eq62
    | (have r₁ := eq62
       have r₂ := eq30994
       grind)
    | exact resolve eq62 eq30994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq30994
  have eq33396 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq33367
  have eq33397 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq33396
  have eq49522 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq31052 eq31043
    | exact resolve eq31043 eq31052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31043 eq31052
  have eq49558 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq49522
  have eq61011 : (τ (k (σ x) (σ y))) = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq33397 eq85
    | exact resolve eq85 eq33397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq33397
  have eq61056 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq56 eq61011
    | exact resolve eq61011 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq61011
  have eq61059 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq61056
       have r₂ := eq61
       grind)
    | exact resolve eq61056 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61056
  have eq61066 : (M.op x y) ≠ (k x y) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq130
       have i₂ := eq61059
       grind)
    | exact superpose eq61059 eq130
    | exact resolve eq130 eq61059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq61059
  have eq61107 : (M.op x y) ≠ (k x y) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq61066
  have eq61133 : (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq61107
       have r₂ := eq675
       grind)
    | exact resolve eq61107 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq61107
  have eq64546 : (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq30582
       have i₂ := eq61133
       grind)
    | exact superpose eq61133 eq30582
    | exact resolve eq30582 eq61133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30582 eq61133
  have eq64600 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by grind
  clear eq64546
  have eq64654 : (τ (σ (M.op x y))) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq64600 eq52
    | exact resolve eq52 eq64600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64600
  have eq64751 : (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq31 eq64654
    | exact resolve eq64654 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq64654
  have eq64752 : (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq64751
  have eq64759 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq64752
       grind)
    | exact superpose eq64752 eq44
    | exact resolve eq44 eq64752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64761 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (k y y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61
       have i₂ := eq64752
       grind)
    | exact superpose eq64752 eq61
    | (have r₁ := eq61
       have r₂ := eq64752
       grind)
    | exact resolve eq61 eq64752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq64752
  have eq64836 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq64761
  have eq64837 : (k x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq64836
  have eq64874 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq64759
    | exact resolve eq64759 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64759
  have eq64909 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq64874 eq49558
    | exact resolve eq49558 eq64874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49558
  have eq64985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq64909
  have eq64991 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq64985
       have r₂ := eq28
       grind)
    | exact resolve eq64985 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64985
  have eq65007 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq64991
       grind)
    | exact superpose eq64991 eq45
    | exact resolve eq45 eq64991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65037 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq913 x
       have i₂ := eq64991
       grind)
    | exact superpose eq64991 eq913
    | (have j0 := eq913 x
       grind)
    | exact resolve eq913 eq64991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913 eq64991
  have eq65050 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq65037
    | exact resolve eq65037 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65037
  have eq65077 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq65007
    | exact resolve eq65007 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65007
  have eq65079 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq65050
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq65050
    | exact resolve eq65050 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65050
  have eq65081 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq65079
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq65079
    | exact resolve eq65079 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq65079
  have eq65083 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq65081
    | exact resolve eq65081 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65081
  have eq65085 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq65083
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq65083
    | exact resolve eq65083 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65083
  have eq65086 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq65085
  have eq65088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq65086
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq65086
    | exact resolve eq65086 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65086
  have eq65091 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq65088
    | exact resolve eq65088 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65088
  have eq65093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq65091
    | exact resolve eq65091 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65091
  have eq65095 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq65093
       have r₂ := eq28
       grind)
    | exact resolve eq65093 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65093
  have eq65149 : (σ (k x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq64837
       grind)
    | exact superpose eq64837 eq74
    | exact resolve eq74 eq64837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq64837
  have eq65225 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq65149
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq65149
    | exact resolve eq65149 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq65149
  have eq69405 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq65225 eq65095
    | exact resolve eq65095 eq65225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65095 eq65225
  have eq69406 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq69405
  have eq69414 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq69406
       have r₂ := eq65077
       grind)
    | exact resolve eq69406 eq65077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65077 eq69406
  have eq69436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq69414 eq64874
    | exact resolve eq64874 eq69414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64874 eq69414
  have eq69458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq69436
  have eq69472 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq69458
       have r₂ := eq28
       grind)
    | exact resolve eq69458 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69458
  have eq69475 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq69472 eq30
    | exact resolve eq30 eq69472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq69472
  have eq69596 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq69475
    | exact resolve eq69475 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq69475
  have eq69597 : x = y := by grind
  clear eq69596
  have eq69861 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq69597
       grind)
    | exact superpose eq69597 eq19
    | exact resolve eq19 eq69597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq69862 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq69597
       grind)
    | exact superpose eq69597 eq25
    | exact resolve eq25 eq69597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq69597
  have eq70228 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq69862
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq69862
    | exact resolve eq69862 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq69862
  have eq70229 : (M.op x y) = (k x x) := by grind
  clear eq69861
  have eq70230 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq70228 eq27
    | exact resolve eq27 eq70228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq70228
  have eq70352 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq70230
  have eq70503 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq70352 eq52
    | exact resolve eq52 eq70352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq70352
  have eq70545 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq70503
       have i₂ := eq70229
       grind)
    | exact superpose eq70229 eq70503
    | exact resolve eq70503 eq70229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70229 eq70503
  have eq70560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70545 eq15
    | exact resolve eq15 eq70545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70545
  have eq70786 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq70560
    | exact resolve eq70560 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq70560
  have eq70856 : False := by grind
  exact eq70856

/-- `x □ y = if X = Y then m(Y,Y) else if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_pxy_pxy_pyy_pyy_pyy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
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
  clear eq36
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ X0 = X1 := by
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
  have eq61 : (M.op x y) ≠ (k x x) ∨ (k x y) = (k y y) ∨ x = y := by
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
  have eq62 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ x) (σ y)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  clear eq86
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 := by
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
  have eq106 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq130 : (M.op x y) ≠ (k y y) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y := by
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
  have eq131 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq88
    | (have j0 := eq88 (σ x) (σ y)
       grind)
    | exact resolve eq88 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq545 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq74
    | exact resolve eq74 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq21 eq545
    | exact resolve eq545 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq673 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
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
  have eq674 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq673
  have eq675 : (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq674
  have eq709 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq97 eq131
    | (have r₁ := eq131
       have r₂ := eq97
       grind)
    | exact resolve eq131 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq709
  have eq711 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq710
  have eq905 : ∀ X0 : G, (σ (k X0 y)) ≠ (k (σ y) (σ y)) ∨ (k (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq41 eq106
    | (have j0 := eq106 (σ X0) (σ y)
       grind)
    | exact resolve eq106 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq106
  have eq913 : ∀ X0 : G, (σ (k X0 y)) ≠ (k (σ y) (σ y)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq905 X0
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq905
    | (have j0 := eq905 X0
       grind)
    | (have r₁ := eq905 y
       have r₂ := eq10 y y
       grind)
    | exact resolve eq905 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq22685 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq546 eq97
    | exact resolve eq97 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq22721 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq22685
       have r₂ := eq28
       grind)
    | exact resolve eq22685 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22685
  have eq22729 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq22721 eq56
    | exact resolve eq56 eq22721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22721
  have eq22740 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq22729
       have i₂ := eq675
       grind)
    | exact superpose eq675 eq22729
    | exact resolve eq22729 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22729
  have eq22771 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq22740
  have eq23062 : (k (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq22771
       grind)
    | exact superpose eq22771 eq44
    | exact resolve eq44 eq22771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22771
  have eq23145 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq23062
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq23062
    | exact resolve eq23062 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23062
  have eq23146 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq23145
  have eq23184 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq23146 eq62
    | (have r₁ := eq62
       have r₂ := eq23146
       grind)
    | exact resolve eq62 eq23146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23146
  have eq23213 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq23184
  have eq23214 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq23213
  have eq23821 : (τ (k (σ x) (σ y))) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq23214 eq85
    | exact resolve eq85 eq23214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23214
  have eq23865 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq56 eq23821
    | exact resolve eq23821 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23821
  have eq23868 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq23865
       have r₂ := eq61
       grind)
    | exact resolve eq23865 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23865
  have eq23870 : (σ (k x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq23868
       grind)
    | exact superpose eq23868 eq74
    | exact resolve eq74 eq23868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23873 : (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq23868
       grind)
    | exact superpose eq23868 eq96
    | exact resolve eq96 eq23868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq23868
  have eq23906 : (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq23873
  have eq23922 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq23870
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq23870
    | exact resolve eq23870 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23870
  have eq23944 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq23906
       grind)
    | exact superpose eq23906 eq45
    | exact resolve eq45 eq23906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23993 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq23944
    | exact resolve eq23944 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23944
  have eq24272 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23993 eq711
    | exact resolve eq711 eq23993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23993
  have eq24280 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq24272
  have eq24284 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq24280
       have r₂ := eq28
       grind)
    | exact resolve eq24280 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24280
  have eq24301 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq23922 eq97
    | exact resolve eq97 eq23922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq24302 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq23922 eq131
    | exact resolve eq131 eq23922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq23922
  have eq24333 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq24302
  have eq24334 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq24301
  have eq24343 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq24333
       have r₂ := eq711
       grind)
    | exact resolve eq24333 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq24333
  have eq26578 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq24284 eq62
    | (have r₁ := eq62
       have r₂ := eq24284
       grind)
    | exact resolve eq62 eq24284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq24284
  have eq26608 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq26578
  have eq26609 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq26608
  have eq42170 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq24343 eq24334
    | exact resolve eq24334 eq24343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24334 eq24343
  have eq42206 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq42170
  have eq53260 : (τ (k (σ x) (σ y))) = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq26609 eq85
    | exact resolve eq85 eq26609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq26609
  have eq53306 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq56 eq53260
    | exact resolve eq53260 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq53260
  have eq53309 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq53306
       have r₂ := eq61
       grind)
    | exact resolve eq53306 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53306
  have eq53316 : (M.op x y) ≠ (k x y) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq130
       have i₂ := eq53309
       grind)
    | exact superpose eq53309 eq130
    | exact resolve eq130 eq53309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq53309
  have eq53346 : (M.op x y) ≠ (k x y) ∨ (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq53316
  have eq53360 : (k x x) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq53346
       have r₂ := eq675
       grind)
    | exact resolve eq53346 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq53346
  have eq56654 : (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq23906
       have i₂ := eq53360
       grind)
    | exact superpose eq53360 eq23906
    | exact resolve eq23906 eq53360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23906 eq53360
  have eq56708 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by grind
  clear eq56654
  have eq56756 : (τ (σ (M.op x y))) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq56708 eq52
    | exact resolve eq52 eq56708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56708
  have eq56854 : (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq31 eq56756
    | exact resolve eq56756 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq56756
  have eq56855 : (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq56854
  have eq56862 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq56855
       grind)
    | exact superpose eq56855 eq44
    | exact resolve eq44 eq56855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56864 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (k y y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61
       have i₂ := eq56855
       grind)
    | exact superpose eq56855 eq61
    | (have r₁ := eq61
       have r₂ := eq56855
       grind)
    | exact resolve eq61 eq56855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq56855
  have eq56934 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq56864
  have eq56935 : (k x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq56934
  have eq56966 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq56862
    | exact resolve eq56862 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56862
  have eq57001 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq56966 eq42206
    | exact resolve eq42206 eq56966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42206
  have eq57078 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq57001
  have eq57084 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq57078
       have r₂ := eq28
       grind)
    | exact resolve eq57078 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57078
  have eq57100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq57084
       grind)
    | exact superpose eq57084 eq45
    | exact resolve eq45 eq57084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57124 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq913 x
       have i₂ := eq57084
       grind)
    | exact superpose eq57084 eq913
    | (have j0 := eq913 x
       grind)
    | exact resolve eq913 eq57084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913 eq57084
  have eq57137 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq57124
    | exact resolve eq57124 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57124
  have eq57158 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq57100
    | exact resolve eq57100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57100
  have eq57160 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57137
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq57137
    | exact resolve eq57137 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57137
  have eq57162 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57160
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq57160
    | exact resolve eq57160 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq57160
  have eq57164 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq57162
    | exact resolve eq57162 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57162
  have eq57166 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57164
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq57164
    | exact resolve eq57164 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57164
  have eq57167 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq57166
  have eq57169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq57167
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq57167
    | exact resolve eq57167 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57167
  have eq57172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq57169
    | exact resolve eq57169 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57169
  have eq57174 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq57172
    | exact resolve eq57172 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57172
  have eq57176 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq57174
       have r₂ := eq28
       grind)
    | exact resolve eq57174 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57174
  have eq57230 : (σ (k x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq56935
       grind)
    | exact superpose eq56935 eq74
    | exact resolve eq74 eq56935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq56935
  have eq57283 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57230
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq57230
    | exact resolve eq57230 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq57230
  have eq61332 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq57283 eq57176
    | exact resolve eq57176 eq57283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57176 eq57283
  have eq61333 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq61332
  have eq61341 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq61333
       have r₂ := eq57158
       grind)
    | exact resolve eq61333 eq57158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57158 eq61333
  have eq61363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq61341 eq56966
    | exact resolve eq56966 eq61341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56966 eq61341
  have eq61386 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq61363
  have eq61400 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq61386
       have r₂ := eq28
       grind)
    | exact resolve eq61386 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61386
  have eq61403 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq61400 eq30
    | exact resolve eq30 eq61400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq61400
  have eq61524 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq61403
    | exact resolve eq61403 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq61403
  have eq61525 : x = y := by grind
  clear eq61524
  have eq61779 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq61525
       grind)
    | exact superpose eq61525 eq19
    | exact resolve eq19 eq61525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq61780 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq61525
       grind)
    | exact superpose eq61525 eq25
    | exact resolve eq25 eq61525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq61525
  have eq62058 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq61780
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq61780
    | exact resolve eq61780 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq61780
  have eq62059 : (M.op x y) = (k x x) := by grind
  clear eq61779
  have eq62060 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq62058 eq27
    | exact resolve eq27 eq62058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq62058
  have eq62182 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq62060
  have eq62318 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq62182 eq52
    | exact resolve eq52 eq62182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq62182
  have eq62361 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq62318
       have i₂ := eq62059
       grind)
    | exact superpose eq62059 eq62318
    | exact resolve eq62318 eq62059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62059 eq62318
  have eq62376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62361 eq15
    | exact resolve eq15 eq62361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62361
  have eq62601 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq62376
    | exact resolve eq62376 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq62376
  have eq62671 : False := by grind
  exact eq62671

/-- `x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_pyx_pyx_pyy_pxx_pyy_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ X0 = X1 := by
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
  have eq61 : (M.op x y) ≠ (k y y) ∨ (k x x) = (k y x) ∨ x = y := by
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
  have eq62 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ y) (σ x)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 X1) = (k (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq48
    | (have j0 := eq48 (σ X0) X1
       grind)
    | exact resolve eq48 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq87 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X1 X1) ∨ (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  clear eq86
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 := by
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
  have eq98 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (k X1 X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (k X0 X0)) = (M.op (σ X0) X1) := by
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
  have eq105 : ∀ X0 X1 : G, (k X1 X1) ≠ (k X0 X0) ∨ (k X1 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X1 X0
       grind)
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
  have eq130 : (M.op x y) ≠ (k x x) ∨ (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y := by
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
  have eq131 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq88
    | (have j0 := eq88 (σ y) (σ x)
       grind)
    | exact resolve eq88 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ (k X1 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq88
    | (have j0 := eq88 X1 X0
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq88 X0 X0
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq68 (M.op X1 X0) (k X1 X1)
       grind)
    | exact resolve eq88 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq88
  have eq135 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ (k X1 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq136 : ∀ X0 X1 : G, (k X1 X1) = (k X1 X0) ∨ (k X1 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq135 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq545 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
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
  have eq546 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
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
  have eq547 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq545
  have eq548 : (k x x) = (k y x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq547
  have eq549 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq21 eq546
    | exact resolve eq546 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq572 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq97 eq62
    | (have r₁ := eq62
       have r₂ := eq97
       grind)
    | exact resolve eq62 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq572
  have eq575 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq574
  have eq909 : ∀ X0 : G, (σ (k X0 x)) ≠ (k (σ x) (σ x)) ∨ (k (σ X0) (σ X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
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
  have eq914 : ∀ X0 : G, (σ (k X0 x)) ≠ (k (σ x) (σ x)) ∨ (σ (k X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq909 X0
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq909
    | (have j0 := eq909 X0
       grind)
    | (have r₁ := eq909 x
       have r₂ := eq10 x x
       grind)
    | exact resolve eq909 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq1184 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (σ X1)) = (k (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (σ X1)
       have i₂ := eq98 X1 (σ X0)
       grind)
    | exact superpose eq98 eq63
    | (have j0 := eq63 X0 (σ X1)
       have j1 := eq98 X1 (σ X0)
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq98 (k X0 X0) (M.op X1 (σ X0))
       grind)
    | (have r₁ := eq63 X0 (σ X0)
       have r₂ := eq98 X0 (σ X0)
       grind)
    | exact resolve eq63 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq98
  have eq1187 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (σ X1)) = (k (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1184 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1192 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (σ X1)) = (k (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1187 X0 X1
       have j1 := eq48 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq1187 X0 X1
       have r₂ := eq48 (k (σ X0) (σ X1)) (σ (k X0 X0))
       grind)
    | (have r₁ := eq1187 X0 X1
       have r₂ := eq48 (σ (k X0 X0)) (k (σ X0) (σ X1))
       grind)
    | (have r₁ := eq1187 X0 X1
       have r₂ := eq48 (σ X0) (σ X1)
       grind)
    | exact resolve eq1187 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq1187
  have eq1203 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (σ X1)) = (k (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1192 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1192
    | (have j0 := eq1192 X0 X1
       grind)
    | (have r₁ := eq1192 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | exact resolve eq1192 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq1210 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1203 X0 X1
       have i₂ := eq10 X1 X1
       grind)
    | exact superpose eq10 eq1203
    | (have j0 := eq1203 X0 X1
       grind)
    | exact resolve eq1203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1214 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X1)) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1210 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1210
    | (have j0 := eq1210 X0 X1
       grind)
    | exact resolve eq1210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1299 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X0 X1) ∨ (k X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       have j1 := eq105 X0 X1
       grind)
    | (have r₁ := eq136 X0 X0
       have r₂ := eq105 X0 X0
       grind)
    | (have r₁ := eq136 X1 X1
       have r₂ := eq105 X1 X1
       grind)
    | (have r₁ := eq136 X0 X1
       have r₂ := eq105 X0 X1
       grind)
    | exact resolve eq136 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq136
  have eq1345 : (k y y) = (k y x) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1299 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1299
    | (have j0 := eq1299 x y
       grind)
    | exact resolve eq1299 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq8040 : ∀ X0 : G, (σ (k y X0)) ≠ (σ (k y x)) ∨ (σ (k y X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1214 y X0
       have i₂ := eq1345
       grind)
    | exact superpose eq1345 eq1214
    | (have j0 := eq1214 y X0
       grind)
    | exact resolve eq1214 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214 eq1345
  have eq8056 : ∀ X0 : G, (σ (k y X0)) ≠ (k (σ y) (σ x)) ∨ (σ (k y X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq8040 X0
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq8040
    | (have j0 := eq8040 X0
       grind)
    | exact resolve eq8040 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8040
  have eq8131 : ∀ X0 : G, (σ X0) = (σ y) ∨ (σ (k y X0)) ≠ (k (σ y) (σ x)) ∨ (σ (k y X0)) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq8056 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8056
    | (have j0 := eq8056 X0
       grind)
    | exact resolve eq8056 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8056
  have eq8194 : ∀ X0 : G, (σ (k y X0)) ≠ (k (σ y) (σ x)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k y X0)) = (σ (k X0 X0)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq8131 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8131
    | (have j0 := eq8131 X0
       grind)
    | exact resolve eq8131 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8131
  have eq22647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq549 eq97
    | exact resolve eq97 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22684 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq22647
       have r₂ := eq28
       grind)
    | exact resolve eq22647 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22647
  have eq22711 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq22684 eq80
    | exact resolve eq80 eq22684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22684
  have eq23024 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq22711
       have i₂ := eq548
       grind)
    | exact superpose eq548 eq22711
    | exact resolve eq22711 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22711
  have eq23045 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq23024
  have eq23698 : (k (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq23045
       grind)
    | exact superpose eq23045 eq44
    | exact resolve eq44 eq23045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23045
  have eq23780 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq23698
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq23698
    | exact resolve eq23698 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23698
  have eq23781 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq23780
  have eq23819 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq23781 eq131
    | (have r₁ := eq131
       have r₂ := eq23781
       grind)
    | exact resolve eq131 eq23781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23781
  have eq23848 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq23819
  have eq23849 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq23848
  have eq33043 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq549 eq23849
    | exact resolve eq23849 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq23849
  have eq33082 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq33043
  have eq33093 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq33082
       have r₂ := eq28
       grind)
    | exact resolve eq33082 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33082
  have eq33099 : (τ (σ (M.op x y))) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq33093 eq80
    | exact resolve eq80 eq33093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33093
  have eq33125 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq31 eq33099
    | exact resolve eq33099 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33099
  have eq33126 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq33125
  have eq33386 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq33126
       grind)
    | exact superpose eq33126 eq73
    | exact resolve eq73 eq33126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33397 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (k y y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq914 y
       have i₂ := eq33126
       grind)
    | exact superpose eq33126 eq914
    | (have j0 := eq914 y
       grind)
    | exact resolve eq914 eq33126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq33126
  have eq33407 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (k y y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq33397
    | exact resolve eq33397 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33397
  have eq33418 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq33386
    | exact resolve eq33386 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33386
  have eq33420 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq33407
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33407
    | exact resolve eq33407 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33407
  have eq33422 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq33420
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq33420
    | exact resolve eq33420 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33420
  have eq33424 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq33422
    | exact resolve eq33422 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33422
  have eq33426 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq33424
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33424
    | exact resolve eq33424 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33424
  have eq33427 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq33426
  have eq33429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq33427
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33427
    | exact resolve eq33427 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33427
  have eq33431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq33429
    | exact resolve eq33429 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33429
  have eq33434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq33431
    | exact resolve eq33431 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33431
  have eq33436 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq33434
       have r₂ := eq28
       grind)
    | exact resolve eq33434 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33434
  have eq33453 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq33418 eq575
    | exact resolve eq575 eq33418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq33461 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq33453
  have eq33467 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq33461
       have r₂ := eq28
       grind)
    | exact resolve eq33461 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33461
  have eq35445 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq33467 eq131
    | (have r₁ := eq131
       have r₂ := eq33467
       grind)
    | exact resolve eq131 eq33467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq33467
  have eq35477 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq35445
  have eq35478 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq35477
  have eq35479 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq35478
       have r₂ := eq33436
       grind)
    | exact resolve eq35478 eq33436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33436 eq35478
  have eq49762 : (k y y) = (τ (k (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq35479 eq85
    | exact resolve eq85 eq35479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq35479
  have eq49804 : (k y y) = (k y x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq80 eq49762
    | exact resolve eq49762 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49762
  have eq50106 : (M.op x y) ≠ (k y x) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq61
       have i₂ := eq49804
       grind)
    | exact superpose eq49804 eq61
    | exact resolve eq61 eq49804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49804
  have eq50142 : (M.op x y) ≠ (k y x) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by grind
  clear eq50106
  have eq50159 : (k x x) = (k y x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq50142
       have r₂ := eq548
       grind)
    | exact resolve eq50142 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq50142
  have eq50192 : (σ (k x x)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq50159
       grind)
    | exact superpose eq50159 eq73
    | exact resolve eq73 eq50159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50159
  have eq50275 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq50192
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq50192
    | exact resolve eq50192 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50192
  have eq50280 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq50275
       have r₂ := eq62
       grind)
    | exact resolve eq50275 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq50275
  have eq51009 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq50280 eq33418
    | exact resolve eq33418 eq50280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33418 eq50280
  have eq51048 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq51009
  have eq51080 : (τ (σ (M.op x y))) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq51048 eq52
    | exact resolve eq52 eq51048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51048
  have eq51177 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq51080
    | exact resolve eq51080 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq51080
  have eq51178 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq51177
  have eq51185 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq51178
       grind)
    | exact superpose eq51178 eq44
    | exact resolve eq44 eq51178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51189 : (M.op x y) ≠ (M.op x y) ∨ (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq130
       have i₂ := eq51178
       grind)
    | exact superpose eq51178 eq130
    | (have r₁ := eq130
       have r₂ := eq51178
       grind)
    | exact resolve eq130 eq51178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq51178
  have eq51231 : (M.op x y) ≠ (M.op x y) ∨ (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51189
  have eq51232 : (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51231
  have eq51263 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq51185
    | exact resolve eq51185 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51185
  have eq67036 : (k (σ y) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq51232
       grind)
    | exact superpose eq51232 eq74
    | exact resolve eq74 eq51232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67068 : (M.op x y) ≠ (k y x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51232
  have eq67094 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq67036
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq67036
    | exact resolve eq67036 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67036
  have eq67135 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq67094 eq97
    | exact resolve eq97 eq67094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67094
  have eq67168 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq67135
  have eq157959 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq67168 eq80
    | exact resolve eq80 eq67168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq428200 : (M.op x y) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq67068
       have i₂ := eq157959
       grind)
    | exact superpose eq157959 eq67068
    | exact resolve eq67068 eq157959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67068
  have eq428215 : (k (σ y) (σ x)) ≠ (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq8194 x
       have i₂ := eq157959
       grind)
    | exact superpose eq157959 eq8194
    | (have j0 := eq8194 x
       grind)
    | exact resolve eq8194 eq157959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8194 eq157959
  have eq428226 : (k (σ y) (σ x)) ≠ (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq428215
  have eq428232 : (M.op x y) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq428200
  have eq428274 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq428226
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq428226
    | exact resolve eq428226 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428226
  have eq428313 : (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq428274
       have r₂ := eq67168
       grind)
    | exact resolve eq428274 eq67168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67168 eq428274
  have eq428339 : (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq428313
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq428313
    | exact resolve eq428313 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428313
  have eq428340 : (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq428339
  have eq428348 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq428340
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq428340
    | exact resolve eq428340 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428340
  have eq428355 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq428348
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq428348
    | exact resolve eq428348 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428348
  have eq428360 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq428355
    | exact resolve eq428355 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428355
  have eq428361 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq428360
  have eq428366 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq428361
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq428361
    | exact resolve eq428361 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428361
  have eq428370 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq428366
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq428366
    | exact resolve eq428366 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428366
  have eq428371 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq428370
  have eq428374 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) := by
    first
    | (have r₁ := eq428371
       have r₂ := eq428232
       grind)
    | exact resolve eq428371 eq428232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428232 eq428371
  have eq428420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq428374 eq51263
    | exact resolve eq51263 eq428374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428374
  have eq428918 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) := by grind
  clear eq428420
  have eq428957 : (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq428918
       have r₂ := eq28
       grind)
    | exact resolve eq428918 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428918
  have eq428963 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61
       have i₂ := eq428957
       grind)
    | exact superpose eq428957 eq61
    | (have r₁ := eq61
       have r₂ := eq428957
       grind)
    | exact resolve eq61 eq428957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq428964 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq428957
       grind)
    | exact superpose eq428957 eq74
    | exact resolve eq74 eq428957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq428957
  have eq429101 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq428963
  have eq429102 : (k x x) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq429101
  have eq429153 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq428964
    | exact resolve eq428964 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428964
  have eq429259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq429153 eq97
    | exact resolve eq97 eq429153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq429153
  have eq429428 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq429259
  have eq429451 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq429428
       have r₂ := eq28
       grind)
    | exact resolve eq429428 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429428
  have eq429464 : (σ (k x x)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq429102
       grind)
    | exact superpose eq429102 eq73
    | exact resolve eq73 eq429102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq429102
  have eq429615 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq429464
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq429464
    | exact resolve eq429464 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq429464
  have eq432458 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq429451 eq429615
    | exact resolve eq429615 eq429451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429451 eq429615
  have eq432471 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq432458
  have eq433562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq432471 eq51263
    | exact resolve eq51263 eq432471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51263 eq432471
  have eq434062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq433562
  have eq434089 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq434062
       have r₂ := eq28
       grind)
    | exact resolve eq434062 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434062
  have eq434092 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq434089 eq30
    | exact resolve eq30 eq434089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq434089
  have eq434299 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq434092
    | exact resolve eq434092 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq434092
  have eq434300 : x = y := by grind
  clear eq434299
  have eq434302 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq434300
       grind)
    | exact superpose eq434300 eq19
    | exact resolve eq19 eq434300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq434303 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq434300
       grind)
    | exact superpose eq434300 eq25
    | exact resolve eq25 eq434300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq434300
  have eq434713 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq434303
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq434303
    | exact resolve eq434303 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq434303
  have eq434714 : (M.op x y) = (k x x) := by grind
  clear eq434302
  have eq434715 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq434713 eq27
    | exact resolve eq27 eq434713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq434713
  have eq434978 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq434715
  have eq435300 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq434978 eq52
    | exact resolve eq52 eq434978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq434978
  have eq435639 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq435300
       have i₂ := eq434714
       grind)
    | exact superpose eq434714 eq435300
    | exact resolve eq435300 eq434714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434714 eq435300
  have eq435684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq435639 eq15
    | exact resolve eq15 eq435639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435639
  have eq436176 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq435684
    | exact resolve eq435684 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq435684
  have eq436314 : False := by grind
  exact eq436314

/-- `x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_pyx_pyx_pyy_pxy_pyy_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ X0 = X1 := by
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
  have eq61 : (M.op x y) ≠ (k y y) ∨ (k x x) = (k y x) ∨ x = y := by
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
  have eq62 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ y) (σ x)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq87 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X1 X1) ∨ (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  clear eq86
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 := by
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
  have eq98 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (k X1 X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (k X0 X0)) = (M.op (σ X0) X1) := by
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
  have eq102 : ∀ X0 X1 : G, (k X1 X1) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 X0
       have i₂ := eq68 X1 X0
       grind)
    | exact superpose eq68 eq48
    | (have j0 := eq48 X1 X0
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq48 X1 X1
       have r₂ := eq68 X1 X1
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq68 (M.op X1 X0) (k X0 X0)
       grind)
    | exact resolve eq48 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (k X1 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X0) ∨ (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (k X1 X1) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq108 : ∀ X0 X1 : G, (k X1 X1) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       have j1 := eq48 X1 X0
       grind)
    | (have r₁ := eq107 X1 X1
       have r₂ := eq48 X1 X1
       grind)
    | (have r₁ := eq107 X0 X1
       have r₂ := eq48 (k X1 X1) (k X0 X0)
       grind)
    | (have r₁ := eq107 X0 X1
       have r₂ := eq48 (k X0 X0) (k X1 X1)
       grind)
    | exact resolve eq107 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq130 : (M.op x y) ≠ (k x x) ∨ (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y := by
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
  have eq131 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq88
    | (have j0 := eq88 (σ y) (σ x)
       grind)
    | exact resolve eq88 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ (k X1 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq88
    | (have j0 := eq88 X1 X0
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq88 X0 X0
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq68 (M.op X1 X0) (k X1 X1)
       grind)
    | exact resolve eq88 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq88
  have eq135 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ (k X1 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq136 : ∀ X0 X1 : G, (k X1 X1) = (k X1 X0) ∨ (k X1 X1) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq135 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq545 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
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
  have eq546 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
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
  have eq547 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq545
  have eq548 : (k x x) = (k y x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq547
  have eq549 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq21 eq546
    | exact resolve eq546 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq572 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq97 eq62
    | (have r₁ := eq62
       have r₂ := eq97
       grind)
    | exact resolve eq62 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq572
  have eq575 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq574
  have eq899 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (k X1 (σ X0)) ∨ (k X1 X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq106 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq106
    | (have j0 := eq106 (σ X0) X1
       grind)
    | exact resolve eq106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq909 : ∀ X0 : G, (σ (k X0 x)) ≠ (k (σ x) (σ x)) ∨ (k (σ X0) (σ X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
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
  have eq914 : ∀ X0 : G, (σ (k X0 x)) ≠ (k (σ x) (σ x)) ∨ (σ (k X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq909 X0
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq909
    | (have j0 := eq909 X0
       grind)
    | (have r₁ := eq909 x
       have r₂ := eq10 x x
       grind)
    | exact resolve eq909 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq1183 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (σ X1) (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (σ (k X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 (σ X1)
       have i₂ := eq98 X1 X0
       grind)
    | exact superpose eq98 eq48
    | (have j0 := eq48 X0 (σ X1)
       have j1 := eq98 X1 X0
       grind)
    | (have r₁ := eq48 (σ X0) (σ X0)
       have r₂ := eq98 X0 (σ X0)
       grind)
    | (have r₁ := eq48 X1 (σ X0)
       have r₂ := eq98 X0 X1
       grind)
    | exact resolve eq48 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1188 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (σ X1) (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq1183 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1193 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (σ X1) (σ X1)) ∨ (σ X1) = X0 ∨ (σ (k X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq1188 X0 X1
       have j1 := eq48 X0 (σ X1)
       grind)
    | (have r₁ := eq1188 (σ X1) X1
       have r₂ := eq48 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq1188 X0 X1
       have r₂ := eq48 (k X0 X0) (k X0 (σ X1))
       grind)
    | (have r₁ := eq1188 X0 X1
       have r₂ := eq48 (k X0 (σ X1)) (k X0 X0)
       grind)
    | exact resolve eq1188 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq1188
  have eq1204 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (σ (k X1 X1)) ∨ (σ X1) = X0 ∨ (σ (k X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1193 X0 X1
       have i₂ := eq10 X1 X1
       grind)
    | exact superpose eq10 eq1193
    | (have j0 := eq1193 X0 X1
       grind)
    | exact resolve eq1193 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq1299 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (k X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       have j1 := eq105 X0 X1
       grind)
    | (have r₁ := eq136 X0 X0
       have r₂ := eq105 X0 X0
       grind)
    | (have r₁ := eq136 X1 X1
       have r₂ := eq105 X1 X1
       grind)
    | (have r₁ := eq136 X0 X1
       have r₂ := eq105 X0 X1
       grind)
    | exact resolve eq136 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq136
  have eq1362 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (k X2 X2) ∨ (k X2 X2) = (k X1 X2) ∨ X1 = X2 ∨ (M.op X2 X1) = (k X1 X2) ∨ X0 = X1 ∨ (k X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq108 X2 X1
       have i₂ := eq1299 X0 X1
       grind)
    | exact superpose eq1299 eq108
    | (have j0 := eq108 X2 X1
       have j1 := eq1299 X0 X1
       grind)
    | (have r₁ := eq108 X0 X1
       have r₂ := eq1299 (k X1 X1) (k X0 X0)
       grind)
    | (have r₁ := eq108 X0 X1
       have r₂ := eq1299 (k X0 X0) (k X1 X1)
       grind)
    | (have r₁ := eq108 X0 X0
       have r₂ := eq1299 X0 X0
       grind)
    | exact resolve eq108 eq1299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1299
  have eq5401 : ∀ X0 : G, (σ (k y X0)) ≠ (σ (k X0 X0)) ∨ (k (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq899
    | (have j0 := eq899 X0 (σ y)
       grind)
    | (have r₁ := eq899 y (σ y)
       have r₂ := eq37 y
       grind)
    | exact resolve eq899 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq5951 : ∀ X0 : G, (σ (k y X0)) ≠ (k (σ y) (σ y)) ∨ (σ (k y X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq1204
    | (have j0 := eq1204 (σ y) X0
       grind)
    | exact resolve eq1204 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1204
  have eq15427 : ∀ X0 : G, (M.op x y) ≠ (k X0 X0) ∨ (k X0 X0) = (k y X0) ∨ y = X0 ∨ (k y X0) = (M.op X0 y) ∨ x = y ∨ (k y y) = (k y x) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1362 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1362
    | (have j0 := eq1362 x y X0
       grind)
    | exact resolve eq1362 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq29278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq549 eq97
    | exact resolve eq97 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29314 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq29278
       have r₂ := eq28
       grind)
    | exact resolve eq29278 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29278
  have eq29337 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq29314 eq80
    | exact resolve eq80 eq29314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29314
  have eq29685 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq29337
       have i₂ := eq548
       grind)
    | exact superpose eq548 eq29337
    | exact resolve eq29337 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29337
  have eq29714 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq29685
  have eq30422 : (k (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq29714
       grind)
    | exact superpose eq29714 eq44
    | exact resolve eq44 eq29714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29714
  have eq30515 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq30422
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq30422
    | exact resolve eq30422 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30422
  have eq30516 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq30515
  have eq30560 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq30516 eq131
    | (have r₁ := eq131
       have r₂ := eq30516
       grind)
    | exact resolve eq131 eq30516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30516
  have eq30588 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq30560
  have eq30589 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq30588
  have eq40171 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq549 eq30589
    | exact resolve eq30589 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq30589
  have eq40209 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq40171
  have eq40220 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq40209
       have r₂ := eq28
       grind)
    | exact resolve eq40209 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40209
  have eq40226 : (τ (σ (M.op x y))) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq40220 eq80
    | exact resolve eq80 eq40220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40220
  have eq40250 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq31 eq40226
    | exact resolve eq40226 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40226
  have eq40251 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq40250
  have eq40521 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq40251
       grind)
    | exact superpose eq40251 eq73
    | exact resolve eq73 eq40251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40542 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (k y y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq914 y
       have i₂ := eq40251
       grind)
    | exact superpose eq40251 eq914
    | (have j0 := eq914 y
       grind)
    | exact resolve eq914 eq40251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq40251
  have eq40550 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (k y y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq40542
    | exact resolve eq40542 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40542
  have eq40571 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq40521
    | exact resolve eq40521 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40521
  have eq40573 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40550
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40550
    | exact resolve eq40550 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40550
  have eq40575 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40573
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq40573
    | exact resolve eq40573 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40573
  have eq40577 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq40575
    | exact resolve eq40575 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40575
  have eq40579 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40577
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40577
    | exact resolve eq40577 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40577
  have eq40580 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq40579
  have eq40582 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40580
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40580
    | exact resolve eq40580 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40580
  have eq40584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq40582
    | exact resolve eq40582 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40582
  have eq40587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq40584
    | exact resolve eq40584 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40584
  have eq40589 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq40587
       have r₂ := eq28
       grind)
    | exact resolve eq40587 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40587
  have eq40606 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq40571 eq575
    | exact resolve eq575 eq40571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq40612 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq40606
  have eq40617 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq40612
       have r₂ := eq28
       grind)
    | exact resolve eq40612 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40612
  have eq42674 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq40617 eq131
    | (have r₁ := eq131
       have r₂ := eq40617
       grind)
    | exact resolve eq131 eq40617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq40617
  have eq42705 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq42674
  have eq42706 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq42705
  have eq42707 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq42706
       have r₂ := eq40589
       grind)
    | exact resolve eq42706 eq40589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40589 eq42706
  have eq57462 : (k y y) = (τ (k (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq42707 eq85
    | exact resolve eq85 eq42707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq42707
  have eq57503 : (k y y) = (k y x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq80 eq57462
    | exact resolve eq57462 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57462
  have eq57815 : (M.op x y) ≠ (k y x) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq61
       have i₂ := eq57503
       grind)
    | exact superpose eq57503 eq61
    | exact resolve eq61 eq57503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq57503
  have eq57862 : (M.op x y) ≠ (k y x) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by grind
  clear eq57815
  have eq57891 : (k x x) = (k y x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq57862
       have r₂ := eq548
       grind)
    | exact resolve eq57862 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq57862
  have eq57924 : (σ (k x x)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq57891
       grind)
    | exact superpose eq57891 eq73
    | exact resolve eq73 eq57891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57891
  have eq58023 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq57924
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq57924
    | exact resolve eq57924 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57924
  have eq58028 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq58023
       have r₂ := eq62
       grind)
    | exact resolve eq58023 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq58023
  have eq58811 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq58028 eq40571
    | exact resolve eq40571 eq58028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40571 eq58028
  have eq58847 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq58811
  have eq58878 : (τ (σ (M.op x y))) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq58847 eq52
    | exact resolve eq52 eq58847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58847
  have eq58974 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq58878
    | exact resolve eq58878 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq58878
  have eq58975 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq58974
  have eq58982 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq58975
       grind)
    | exact superpose eq58975 eq44
    | exact resolve eq44 eq58975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58986 : (M.op x y) ≠ (M.op x y) ∨ (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq130
       have i₂ := eq58975
       grind)
    | exact superpose eq58975 eq130
    | (have r₁ := eq130
       have r₂ := eq58975
       grind)
    | exact resolve eq130 eq58975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq59033 : (M.op x y) ≠ (M.op x y) ∨ (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq58986
  have eq59034 : (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq59033
  have eq59071 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq58982
    | exact resolve eq58982 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58982
  have eq75271 : (k (σ y) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq59034
       grind)
    | exact superpose eq59034 eq74
    | exact resolve eq74 eq59034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59034
  have eq75352 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq75271
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq75271
    | exact resolve eq75271 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq75271
  have eq75393 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq75352 eq97
    | exact resolve eq97 eq75352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq75425 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq75393
  have eq169848 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq75425 eq80
    | exact resolve eq80 eq75425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq353303 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (k y y) = (k y x) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15427 x
       have i₂ := eq58975
       grind)
    | exact superpose eq58975 eq15427
    | (have j0 := eq15427 x
       grind)
    | (have r₁ := eq15427 x
       have r₂ := eq58975
       grind)
    | exact resolve eq15427 eq58975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15427 eq58975
  have eq353338 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (k y y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq353303
  have eq353339 : (M.op x y) = (k y x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (k y y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq353338
  have eq353413 : (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ x = y ∨ (k y y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq353339
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq353339
    | exact resolve eq353339 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353339
  have eq353414 : (k y y) = (k y x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq353413
  have eq464741 : (k (σ y) (σ y)) ≠ (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq5951 x
       have i₂ := eq169848
       grind)
    | exact superpose eq169848 eq5951
    | (have j0 := eq5951 x
       grind)
    | exact resolve eq5951 eq169848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5951 eq169848
  have eq464802 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq464741
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq464741
    | exact resolve eq464741 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464741
  have eq464849 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq464802
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq464802
    | exact resolve eq464802 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464802
  have eq464884 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq464849
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq464849
    | exact resolve eq464849 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464849
  have eq464885 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq464884
  have eq464890 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq464885
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq464885
    | exact resolve eq464885 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464885
  have eq464891 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq464890
  have eq464895 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq464891
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq464891
    | exact resolve eq464891 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464891
  have eq464898 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq464895
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq464895
    | exact resolve eq464895 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464895
  have eq464900 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq27 eq464898
    | exact resolve eq464898 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464898
  have eq464901 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq464900
  have eq464911 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq75352 eq464901
    | exact resolve eq464901 eq75352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75352 eq464901
  have eq464914 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq464911
  have eq464927 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have r₁ := eq464914
       have r₂ := eq75425
       grind)
    | exact resolve eq464914 eq75425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75425 eq464914
  have eq465065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq464927 eq59071
    | exact resolve eq59071 eq464927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464927
  have eq465584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) := by grind
  clear eq465065
  have eq465629 : (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq465584
       have r₂ := eq28
       grind)
    | exact resolve eq465584 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465584
  have eq465638 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq465629
       grind)
    | exact superpose eq465629 eq74
    | exact resolve eq74 eq465629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq465675 : (M.op x y) = (k y x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq353414
       have i₂ := eq465629
       grind)
    | exact superpose eq465629 eq353414
    | exact resolve eq353414 eq465629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353414 eq465629
  have eq465809 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq465675
  have eq465878 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq465638
    | exact resolve eq465638 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465638
  have eq466109 : (σ (M.op x y)) ≠ (σ (k x x)) ∨ (k (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5401 x
       have i₂ := eq465809
       grind)
    | exact superpose eq465809 eq5401
    | (have j0 := eq5401 x
       grind)
    | exact resolve eq5401 eq465809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5401 eq465809
  have eq466143 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (k (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq466109
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq466109
    | exact resolve eq466109 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq466109
  have eq466191 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (k (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq466143
    | exact resolve eq466143 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466143
  have eq466203 : (k (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq466191
       have r₂ := eq59071
       grind)
    | exact resolve eq466191 eq59071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59071 eq466191
  have eq466213 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq466203
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq466203
    | exact resolve eq466203 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466203
  have eq466224 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq466213
    | exact resolve eq466213 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466213
  have eq466236 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq466224
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq466224
    | exact resolve eq466224 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466224
  have eq466237 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq466236
  have eq466247 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq466237
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq466237
    | exact resolve eq466237 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466237
  have eq466255 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq466247
    | exact resolve eq466247 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466247
  have eq466263 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq466255
    | exact resolve eq466255 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466255
  have eq466268 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq466263
       have r₂ := eq28
       grind)
    | exact resolve eq466263 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466263
  have eq466800 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq466268 eq465878
    | exact resolve eq465878 eq466268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465878 eq466268
  have eq466919 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq466800
  have eq466957 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq466919
       have r₂ := eq28
       grind)
    | exact resolve eq466919 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466919
  have eq466963 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq466957 eq30
    | exact resolve eq30 eq466957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq466957
  have eq467175 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq466963
    | exact resolve eq466963 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq466963
  have eq467176 : x = y := by grind
  clear eq467175
  have eq467266 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq467176
       grind)
    | exact superpose eq467176 eq19
    | exact resolve eq19 eq467176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq467267 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq467176
       grind)
    | exact superpose eq467176 eq25
    | exact resolve eq25 eq467176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq467176
  have eq467768 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq467267
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq467267
    | exact resolve eq467267 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq467267
  have eq467769 : (M.op x y) = (k x x) := by grind
  clear eq467266
  have eq467770 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq467768 eq27
    | exact resolve eq27 eq467768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq467768
  have eq468042 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq467770
  have eq468699 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq468042 eq52
    | exact resolve eq52 eq468042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq468042
  have eq469062 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq468699
       have i₂ := eq467769
       grind)
    | exact superpose eq467769 eq468699
    | exact resolve eq468699 eq467769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467769 eq468699
  have eq469108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq469062 eq15
    | exact resolve eq15 eq469062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469062
  have eq469598 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq469108
    | exact resolve eq469108 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq469108
  have eq469734 : False := by grind
  exact eq469734

/-- `x □ y = if X = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_pyx_pyx_pyy_pyx_pyy_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ X0 = X1 := by
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
  have eq61 : (M.op x y) ≠ (k y y) ∨ (k x x) = (k y x) ∨ x = y := by
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
  have eq62 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ y) (σ x)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 X1) = (k (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq48
    | (have j0 := eq48 (σ X0) X1
       grind)
    | exact resolve eq48 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq87 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X1 X1) ∨ (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  clear eq86
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 := by
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
  have eq98 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (k X1 X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (k X0 X0)) = (M.op (σ X0) X1) := by
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
  have eq105 : ∀ X0 X1 : G, (k X1 X1) ≠ (k X0 X0) ∨ (k X1 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X1 X0
       grind)
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
  have eq130 : (M.op x y) ≠ (k x x) ∨ (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y := by
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
  have eq131 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq88
    | (have j0 := eq88 (σ y) (σ x)
       grind)
    | exact resolve eq88 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ (k X1 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq88
    | (have j0 := eq88 X1 X0
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq88 X0 X0
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq68 (M.op X1 X0) (k X1 X1)
       grind)
    | exact resolve eq88 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq88
  have eq135 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ (k X1 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq136 : ∀ X0 X1 : G, (k X1 X1) = (k X1 X0) ∨ (k X1 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq135 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq545 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
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
  have eq546 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
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
  have eq547 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq545
  have eq548 : (k x x) = (k y x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq547
  have eq549 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq21 eq546
    | exact resolve eq546 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq572 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq97 eq62
    | (have r₁ := eq62
       have r₂ := eq97
       grind)
    | exact resolve eq62 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq572
  have eq575 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq574
  have eq909 : ∀ X0 : G, (σ (k X0 x)) ≠ (k (σ x) (σ x)) ∨ (k (σ X0) (σ X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
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
  have eq914 : ∀ X0 : G, (σ (k X0 x)) ≠ (k (σ x) (σ x)) ∨ (σ (k X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq909 X0
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq909
    | (have j0 := eq909 X0
       grind)
    | (have r₁ := eq909 x
       have r₂ := eq10 x x
       grind)
    | exact resolve eq909 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq1184 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (σ X1)) = (k (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (σ X1)
       have i₂ := eq98 X1 (σ X0)
       grind)
    | exact superpose eq98 eq63
    | (have j0 := eq63 X0 (σ X1)
       have j1 := eq98 X1 (σ X0)
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq98 (k X0 X0) (M.op X1 (σ X0))
       grind)
    | (have r₁ := eq63 X0 (σ X0)
       have r₂ := eq98 X0 (σ X0)
       grind)
    | exact resolve eq63 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq98
  have eq1187 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (σ X1)) = (k (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1184 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1192 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (σ X1)) = (k (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1187 X0 X1
       have j1 := eq48 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq1187 X0 X1
       have r₂ := eq48 (k (σ X0) (σ X1)) (σ (k X0 X0))
       grind)
    | (have r₁ := eq1187 X0 X1
       have r₂ := eq48 (σ (k X0 X0)) (k (σ X0) (σ X1))
       grind)
    | (have r₁ := eq1187 X0 X1
       have r₂ := eq48 (σ X0) (σ X1)
       grind)
    | exact resolve eq1187 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq1187
  have eq1203 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (σ X1)) = (k (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1192 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1192
    | (have j0 := eq1192 X0 X1
       grind)
    | (have r₁ := eq1192 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | exact resolve eq1192 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq1210 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1203 X0 X1
       have i₂ := eq10 X1 X1
       grind)
    | exact superpose eq10 eq1203
    | (have j0 := eq1203 X0 X1
       grind)
    | exact resolve eq1203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1214 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X1)) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1210 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1210
    | (have j0 := eq1210 X0 X1
       grind)
    | exact resolve eq1210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1299 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X0 X1) ∨ (k X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       have j1 := eq105 X0 X1
       grind)
    | (have r₁ := eq136 X0 X0
       have r₂ := eq105 X0 X0
       grind)
    | (have r₁ := eq136 X1 X1
       have r₂ := eq105 X1 X1
       grind)
    | (have r₁ := eq136 X0 X1
       have r₂ := eq105 X0 X1
       grind)
    | exact resolve eq136 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq136
  have eq1345 : (k y y) = (k y x) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1299 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1299
    | (have j0 := eq1299 x y
       grind)
    | exact resolve eq1299 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq8040 : ∀ X0 : G, (σ (k y X0)) ≠ (σ (k y x)) ∨ (σ (k y X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1214 y X0
       have i₂ := eq1345
       grind)
    | exact superpose eq1345 eq1214
    | (have j0 := eq1214 y X0
       grind)
    | exact resolve eq1214 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214 eq1345
  have eq8056 : ∀ X0 : G, (σ (k y X0)) ≠ (k (σ y) (σ x)) ∨ (σ (k y X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq8040 X0
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq8040
    | (have j0 := eq8040 X0
       grind)
    | exact resolve eq8040 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8040
  have eq8131 : ∀ X0 : G, (σ X0) = (σ y) ∨ (σ (k y X0)) ≠ (k (σ y) (σ x)) ∨ (σ (k y X0)) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq8056 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8056
    | (have j0 := eq8056 X0
       grind)
    | exact resolve eq8056 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8056
  have eq8194 : ∀ X0 : G, (σ (k y X0)) ≠ (k (σ y) (σ x)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k y X0)) = (σ (k X0 X0)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq8131 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8131
    | (have j0 := eq8131 X0
       grind)
    | exact resolve eq8131 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8131
  have eq22647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq549 eq97
    | exact resolve eq97 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22684 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq22647
       have r₂ := eq28
       grind)
    | exact resolve eq22647 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22647
  have eq22711 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq22684 eq80
    | exact resolve eq80 eq22684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22684
  have eq23024 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq22711
       have i₂ := eq548
       grind)
    | exact superpose eq548 eq22711
    | exact resolve eq22711 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22711
  have eq23045 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq23024
  have eq23698 : (k (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq23045
       grind)
    | exact superpose eq23045 eq44
    | exact resolve eq44 eq23045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23045
  have eq23780 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq23698
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq23698
    | exact resolve eq23698 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23698
  have eq23781 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq23780
  have eq23819 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq23781 eq131
    | (have r₁ := eq131
       have r₂ := eq23781
       grind)
    | exact resolve eq131 eq23781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23781
  have eq23848 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq23819
  have eq23849 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq23848
  have eq33043 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq549 eq23849
    | exact resolve eq23849 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq23849
  have eq33082 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq33043
  have eq33093 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq33082
       have r₂ := eq28
       grind)
    | exact resolve eq33082 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33082
  have eq33099 : (τ (σ (M.op x y))) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq33093 eq80
    | exact resolve eq80 eq33093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33093
  have eq33125 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq31 eq33099
    | exact resolve eq33099 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33099
  have eq33126 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq33125
  have eq33386 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq33126
       grind)
    | exact superpose eq33126 eq73
    | exact resolve eq73 eq33126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33397 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (k y y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq914 y
       have i₂ := eq33126
       grind)
    | exact superpose eq33126 eq914
    | (have j0 := eq914 y
       grind)
    | exact resolve eq914 eq33126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq33126
  have eq33407 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (k y y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq33397
    | exact resolve eq33397 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33397
  have eq33418 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq33386
    | exact resolve eq33386 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33386
  have eq33420 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq33407
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33407
    | exact resolve eq33407 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33407
  have eq33422 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq33420
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq33420
    | exact resolve eq33420 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33420
  have eq33424 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq33422
    | exact resolve eq33422 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33422
  have eq33426 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq33424
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33424
    | exact resolve eq33424 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33424
  have eq33427 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq33426
  have eq33429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq33427
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33427
    | exact resolve eq33427 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33427
  have eq33431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq33429
    | exact resolve eq33429 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33429
  have eq33434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq33431
    | exact resolve eq33431 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33431
  have eq33436 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq33434
       have r₂ := eq28
       grind)
    | exact resolve eq33434 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33434
  have eq33453 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq33418 eq575
    | exact resolve eq575 eq33418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq33461 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq33453
  have eq33467 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq33461
       have r₂ := eq28
       grind)
    | exact resolve eq33461 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33461
  have eq35445 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq33467 eq131
    | (have r₁ := eq131
       have r₂ := eq33467
       grind)
    | exact resolve eq131 eq33467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq33467
  have eq35477 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq35445
  have eq35478 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq35477
  have eq35479 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq35478
       have r₂ := eq33436
       grind)
    | exact resolve eq35478 eq33436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33436 eq35478
  have eq49762 : (k y y) = (τ (k (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq35479 eq85
    | exact resolve eq85 eq35479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq35479
  have eq49804 : (k y y) = (k y x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq80 eq49762
    | exact resolve eq49762 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49762
  have eq50106 : (M.op x y) ≠ (k y x) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq61
       have i₂ := eq49804
       grind)
    | exact superpose eq49804 eq61
    | exact resolve eq61 eq49804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49804
  have eq50142 : (M.op x y) ≠ (k y x) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by grind
  clear eq50106
  have eq50159 : (k x x) = (k y x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq50142
       have r₂ := eq548
       grind)
    | exact resolve eq50142 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq50142
  have eq50192 : (σ (k x x)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq50159
       grind)
    | exact superpose eq50159 eq73
    | exact resolve eq73 eq50159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50159
  have eq50275 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq50192
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq50192
    | exact resolve eq50192 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50192
  have eq50280 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq50275
       have r₂ := eq62
       grind)
    | exact resolve eq50275 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq50275
  have eq51009 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq50280 eq33418
    | exact resolve eq33418 eq50280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33418 eq50280
  have eq51048 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq51009
  have eq51080 : (τ (σ (M.op x y))) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq51048 eq52
    | exact resolve eq52 eq51048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51048
  have eq51177 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq51080
    | exact resolve eq51080 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq51080
  have eq51178 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq51177
  have eq51185 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq51178
       grind)
    | exact superpose eq51178 eq44
    | exact resolve eq44 eq51178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51189 : (M.op x y) ≠ (M.op x y) ∨ (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq130
       have i₂ := eq51178
       grind)
    | exact superpose eq51178 eq130
    | (have r₁ := eq130
       have r₂ := eq51178
       grind)
    | exact resolve eq130 eq51178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq51178
  have eq51231 : (M.op x y) ≠ (M.op x y) ∨ (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51189
  have eq51232 : (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51231
  have eq51263 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq51185
    | exact resolve eq51185 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51185
  have eq67036 : (k (σ y) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq51232
       grind)
    | exact superpose eq51232 eq74
    | exact resolve eq74 eq51232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67068 : (M.op x y) ≠ (k y x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51232
  have eq67094 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq67036
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq67036
    | exact resolve eq67036 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67036
  have eq67135 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq67094 eq97
    | exact resolve eq97 eq67094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67094
  have eq67168 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq67135
  have eq157959 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq67168 eq80
    | exact resolve eq80 eq67168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq428200 : (M.op x y) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq67068
       have i₂ := eq157959
       grind)
    | exact superpose eq157959 eq67068
    | exact resolve eq67068 eq157959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67068
  have eq428215 : (k (σ y) (σ x)) ≠ (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq8194 x
       have i₂ := eq157959
       grind)
    | exact superpose eq157959 eq8194
    | (have j0 := eq8194 x
       grind)
    | exact resolve eq8194 eq157959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8194 eq157959
  have eq428226 : (k (σ y) (σ x)) ≠ (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq428215
  have eq428232 : (M.op x y) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq428200
  have eq428274 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq428226
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq428226
    | exact resolve eq428226 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428226
  have eq428313 : (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq428274
       have r₂ := eq67168
       grind)
    | exact resolve eq428274 eq67168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67168 eq428274
  have eq428339 : (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq428313
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq428313
    | exact resolve eq428313 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428313
  have eq428340 : (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq428339
  have eq428348 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq428340
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq428340
    | exact resolve eq428340 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428340
  have eq428355 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq428348
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq428348
    | exact resolve eq428348 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428348
  have eq428360 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq428355
    | exact resolve eq428355 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428355
  have eq428361 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq428360
  have eq428366 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq428361
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq428361
    | exact resolve eq428361 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428361
  have eq428370 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq428366
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq428366
    | exact resolve eq428366 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428366
  have eq428371 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq428370
  have eq428374 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) := by
    first
    | (have r₁ := eq428371
       have r₂ := eq428232
       grind)
    | exact resolve eq428371 eq428232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428232 eq428371
  have eq428420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq428374 eq51263
    | exact resolve eq51263 eq428374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428374
  have eq428918 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) := by grind
  clear eq428420
  have eq428957 : (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq428918
       have r₂ := eq28
       grind)
    | exact resolve eq428918 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428918
  have eq428963 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61
       have i₂ := eq428957
       grind)
    | exact superpose eq428957 eq61
    | (have r₁ := eq61
       have r₂ := eq428957
       grind)
    | exact resolve eq61 eq428957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq428964 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq428957
       grind)
    | exact superpose eq428957 eq74
    | exact resolve eq74 eq428957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq428957
  have eq429101 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq428963
  have eq429102 : (k x x) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq429101
  have eq429153 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq428964
    | exact resolve eq428964 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428964
  have eq429259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq429153 eq97
    | exact resolve eq97 eq429153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq429153
  have eq429428 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq429259
  have eq429451 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq429428
       have r₂ := eq28
       grind)
    | exact resolve eq429428 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429428
  have eq429464 : (σ (k x x)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq429102
       grind)
    | exact superpose eq429102 eq73
    | exact resolve eq73 eq429102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq429102
  have eq429615 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq429464
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq429464
    | exact resolve eq429464 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq429464
  have eq432458 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq429451 eq429615
    | exact resolve eq429615 eq429451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429451 eq429615
  have eq432471 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq432458
  have eq433562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq432471 eq51263
    | exact resolve eq51263 eq432471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51263 eq432471
  have eq434062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq433562
  have eq434089 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq434062
       have r₂ := eq28
       grind)
    | exact resolve eq434062 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434062
  have eq434092 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq434089 eq30
    | exact resolve eq30 eq434089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq434089
  have eq434299 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq434092
    | exact resolve eq434092 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq434092
  have eq434300 : x = y := by grind
  clear eq434299
  have eq434302 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq434300
       grind)
    | exact superpose eq434300 eq19
    | exact resolve eq19 eq434300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq434303 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq434300
       grind)
    | exact superpose eq434300 eq25
    | exact resolve eq25 eq434300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq434300
  have eq434713 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq434303
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq434303
    | exact resolve eq434303 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq434303
  have eq434714 : (M.op x y) = (k x x) := by grind
  clear eq434302
  have eq434715 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq434713 eq27
    | exact resolve eq27 eq434713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq434713
  have eq434978 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq434715
  have eq435300 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq434978 eq52
    | exact resolve eq52 eq434978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq434978
  have eq435639 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq435300
       have i₂ := eq434714
       grind)
    | exact superpose eq434714 eq435300
    | exact resolve eq435300 eq434714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434714 eq435300
  have eq435684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq435639 eq15
    | exact resolve eq15 eq435639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435639
  have eq436176 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq435684
    | exact resolve eq435684 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq435684
  have eq436314 : False := by grind
  exact eq436314

/-- `x □ y = if X = Y then m(Y,Y) else if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_pyx_pyx_pyy_pyy_pyy_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X1) = (k X1 X1) ∨ X0 = X1 := by
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
  have eq61 : (M.op x y) ≠ (k y y) ∨ (k x x) = (k y x) ∨ x = y := by
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
  have eq62 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq48
    | (have j0 := eq48 (σ y) (σ x)
       grind)
    | exact resolve eq48 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 X1) = (k (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq48
    | (have j0 := eq48 (σ X0) X1
       grind)
    | exact resolve eq48 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 ∨ (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq87 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X1 X1) ∨ (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  clear eq86
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X1 X1) ∨ (k X0 X1) = (k X0 X0) ∨ (M.op X1 X0) = (k X0 X0) ∨ X0 = X1 := by
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
  have eq98 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (k X1 X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (k X0 X0)) = (M.op (σ X0) X1) := by
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
  have eq105 : ∀ X0 X1 : G, (k X1 X1) ≠ (k X0 X0) ∨ (k X1 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X1 X0
       grind)
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
  have eq130 : (M.op x y) ≠ (k x x) ∨ (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y := by
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
  have eq131 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq88
    | (have j0 := eq88 (σ y) (σ x)
       grind)
    | exact resolve eq88 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ (k X1 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq88
    | (have j0 := eq88 X1 X0
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq88 X0 X0
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq68 (M.op X1 X0) (k X1 X1)
       grind)
    | exact resolve eq88 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq88
  have eq135 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 X1) = (k X1 X0) ∨ (k X1 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq136 : ∀ X0 X1 : G, (k X1 X1) = (k X1 X0) ∨ (k X1 X1) = (k X0 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq135 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq545 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
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
  have eq546 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
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
  have eq547 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq545
  have eq548 : (k x x) = (k y x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq547
  have eq549 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq21 eq546
    | exact resolve eq546 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq572 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq97 eq62
    | (have r₁ := eq62
       have r₂ := eq97
       grind)
    | exact resolve eq62 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq572
  have eq575 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq574
  have eq909 : ∀ X0 : G, (σ (k X0 x)) ≠ (k (σ x) (σ x)) ∨ (k (σ X0) (σ X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
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
  have eq914 : ∀ X0 : G, (σ (k X0 x)) ≠ (k (σ x) (σ x)) ∨ (σ (k X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq909 X0
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq909
    | (have j0 := eq909 X0
       grind)
    | (have r₁ := eq909 x
       have r₂ := eq10 x x
       grind)
    | exact resolve eq909 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq1184 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (σ X1)) = (k (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (σ X1)
       have i₂ := eq98 X1 (σ X0)
       grind)
    | exact superpose eq98 eq63
    | (have j0 := eq63 X0 (σ X1)
       have j1 := eq98 X1 (σ X0)
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq98 (k X0 X0) (M.op X1 (σ X0))
       grind)
    | (have r₁ := eq63 X0 (σ X0)
       have r₂ := eq98 X0 (σ X0)
       grind)
    | exact resolve eq63 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq98
  have eq1187 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (σ X1)) = (k (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1184 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1192 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (σ X1)) = (k (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1187 X0 X1
       have j1 := eq48 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq1187 X0 X1
       have r₂ := eq48 (k (σ X0) (σ X1)) (σ (k X0 X0))
       grind)
    | (have r₁ := eq1187 X0 X1
       have r₂ := eq48 (σ (k X0 X0)) (k (σ X0) (σ X1))
       grind)
    | (have r₁ := eq1187 X0 X1
       have r₂ := eq48 (σ X0) (σ X1)
       grind)
    | exact resolve eq1187 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq1187
  have eq1203 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (σ X1)) = (k (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1192 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1192
    | (have j0 := eq1192 X0 X1
       grind)
    | (have r₁ := eq1192 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | exact resolve eq1192 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq1210 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1203 X0 X1
       have i₂ := eq10 X1 X1
       grind)
    | exact superpose eq10 eq1203
    | (have j0 := eq1203 X0 X1
       grind)
    | exact resolve eq1203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1214 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X1)) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1210 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1210
    | (have j0 := eq1210 X0 X1
       grind)
    | exact resolve eq1210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1299 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (M.op X0 X1) ∨ (k X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       have j1 := eq105 X0 X1
       grind)
    | (have r₁ := eq136 X0 X0
       have r₂ := eq105 X0 X0
       grind)
    | (have r₁ := eq136 X1 X1
       have r₂ := eq105 X1 X1
       grind)
    | (have r₁ := eq136 X0 X1
       have r₂ := eq105 X0 X1
       grind)
    | exact resolve eq136 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq136
  have eq1345 : (k y y) = (k y x) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1299 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1299
    | (have j0 := eq1299 x y
       grind)
    | exact resolve eq1299 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq8040 : ∀ X0 : G, (σ (k y X0)) ≠ (σ (k y x)) ∨ (σ (k y X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1214 y X0
       have i₂ := eq1345
       grind)
    | exact superpose eq1345 eq1214
    | (have j0 := eq1214 y X0
       grind)
    | exact resolve eq1214 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214 eq1345
  have eq8056 : ∀ X0 : G, (σ (k y X0)) ≠ (k (σ y) (σ x)) ∨ (σ (k y X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq8040 X0
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq8040
    | (have j0 := eq8040 X0
       grind)
    | exact resolve eq8040 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8040
  have eq8131 : ∀ X0 : G, (σ X0) = (σ y) ∨ (σ (k y X0)) ≠ (k (σ y) (σ x)) ∨ (σ (k y X0)) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq8056 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8056
    | (have j0 := eq8056 X0
       grind)
    | exact resolve eq8056 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8056
  have eq8194 : ∀ X0 : G, (σ (k y X0)) ≠ (k (σ y) (σ x)) ∨ (σ X0) = (σ y) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k y X0)) = (σ (k X0 X0)) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq8131 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8131
    | (have j0 := eq8131 X0
       grind)
    | exact resolve eq8131 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8131
  have eq22647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq549 eq97
    | exact resolve eq97 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22684 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq22647
       have r₂ := eq28
       grind)
    | exact resolve eq22647 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22647
  have eq22711 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq22684 eq80
    | exact resolve eq80 eq22684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22684
  have eq23024 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq22711
       have i₂ := eq548
       grind)
    | exact superpose eq548 eq22711
    | exact resolve eq22711 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22711
  have eq23045 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq23024
  have eq23698 : (k (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq23045
       grind)
    | exact superpose eq23045 eq44
    | exact resolve eq44 eq23045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23045
  have eq23780 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq23698
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq23698
    | exact resolve eq23698 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23698
  have eq23781 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq23780
  have eq23819 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq23781 eq131
    | (have r₁ := eq131
       have r₂ := eq23781
       grind)
    | exact resolve eq131 eq23781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23781
  have eq23848 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq23819
  have eq23849 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq23848
  have eq33043 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq549 eq23849
    | exact resolve eq23849 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq23849
  have eq33082 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq33043
  have eq33093 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq33082
       have r₂ := eq28
       grind)
    | exact resolve eq33082 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33082
  have eq33099 : (τ (σ (M.op x y))) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq33093 eq80
    | exact resolve eq80 eq33093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33093
  have eq33125 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq31 eq33099
    | exact resolve eq33099 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33099
  have eq33126 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq33125
  have eq33386 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq33126
       grind)
    | exact superpose eq33126 eq73
    | exact resolve eq73 eq33126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33397 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (k y y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq914 y
       have i₂ := eq33126
       grind)
    | exact superpose eq33126 eq914
    | (have j0 := eq914 y
       grind)
    | exact resolve eq914 eq33126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq33126
  have eq33407 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (k y y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq33397
    | exact resolve eq33397 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33397
  have eq33418 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq33386
    | exact resolve eq33386 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33386
  have eq33420 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq33407
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33407
    | exact resolve eq33407 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33407
  have eq33422 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq33420
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq33420
    | exact resolve eq33420 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33420
  have eq33424 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq33422
    | exact resolve eq33422 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33422
  have eq33426 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq33424
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33424
    | exact resolve eq33424 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33424
  have eq33427 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq33426
  have eq33429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq33427
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33427
    | exact resolve eq33427 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33427
  have eq33431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq27 eq33429
    | exact resolve eq33429 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33429
  have eq33434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq21 eq33431
    | exact resolve eq33431 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33431
  have eq33436 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq33434
       have r₂ := eq28
       grind)
    | exact resolve eq33434 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33434
  have eq33453 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq33418 eq575
    | exact resolve eq575 eq33418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq33461 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq33453
  have eq33467 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq33461
       have r₂ := eq28
       grind)
    | exact resolve eq33461 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33461
  have eq35445 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq33467 eq131
    | (have r₁ := eq131
       have r₂ := eq33467
       grind)
    | exact resolve eq131 eq33467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq33467
  have eq35477 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq35445
  have eq35478 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq35477
  have eq35479 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq35478
       have r₂ := eq33436
       grind)
    | exact resolve eq35478 eq33436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33436 eq35478
  have eq49762 : (k y y) = (τ (k (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq35479 eq85
    | exact resolve eq85 eq35479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq35479
  have eq49804 : (k y y) = (k y x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq80 eq49762
    | exact resolve eq49762 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49762
  have eq50106 : (M.op x y) ≠ (k y x) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq61
       have i₂ := eq49804
       grind)
    | exact superpose eq49804 eq61
    | exact resolve eq61 eq49804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49804
  have eq50142 : (M.op x y) ≠ (k y x) ∨ (k x x) = (k y x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by grind
  clear eq50106
  have eq50159 : (k x x) = (k y x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq50142
       have r₂ := eq548
       grind)
    | exact resolve eq50142 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq50142
  have eq50192 : (σ (k x x)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq50159
       grind)
    | exact superpose eq50159 eq73
    | exact resolve eq73 eq50159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50159
  have eq50275 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq50192
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq50192
    | exact resolve eq50192 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50192
  have eq50280 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq50275
       have r₂ := eq62
       grind)
    | exact resolve eq50275 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq50275
  have eq51009 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq50280 eq33418
    | exact resolve eq33418 eq50280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33418 eq50280
  have eq51048 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq51009
  have eq51080 : (τ (σ (M.op x y))) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq51048 eq52
    | exact resolve eq52 eq51048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51048
  have eq51177 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq51080
    | exact resolve eq51080 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq51080
  have eq51178 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq51177
  have eq51185 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq51178
       grind)
    | exact superpose eq51178 eq44
    | exact resolve eq44 eq51178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51189 : (M.op x y) ≠ (M.op x y) ∨ (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq130
       have i₂ := eq51178
       grind)
    | exact superpose eq51178 eq130
    | (have r₁ := eq130
       have r₂ := eq51178
       grind)
    | exact resolve eq130 eq51178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq51178
  have eq51231 : (M.op x y) ≠ (M.op x y) ∨ (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51189
  have eq51232 : (k y y) = (k y x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51231
  have eq51263 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq51185
    | exact resolve eq51185 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51185
  have eq67036 : (k (σ y) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq51232
       grind)
    | exact superpose eq51232 eq74
    | exact resolve eq74 eq51232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67068 : (M.op x y) ≠ (k y x) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq51232
  have eq67094 : (k (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq67036
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq67036
    | exact resolve eq67036 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67036
  have eq67135 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq67094 eq97
    | exact resolve eq97 eq67094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67094
  have eq67168 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by grind
  clear eq67135
  have eq157959 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq67168 eq80
    | exact resolve eq80 eq67168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq428200 : (M.op x y) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq67068
       have i₂ := eq157959
       grind)
    | exact superpose eq157959 eq67068
    | exact resolve eq67068 eq157959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67068
  have eq428215 : (k (σ y) (σ x)) ≠ (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq8194 x
       have i₂ := eq157959
       grind)
    | exact superpose eq157959 eq8194
    | (have j0 := eq8194 x
       grind)
    | exact resolve eq8194 eq157959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8194 eq157959
  have eq428226 : (k (σ y) (σ x)) ≠ (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq428215
  have eq428232 : (M.op x y) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq428200
  have eq428274 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq428226
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq428226
    | exact resolve eq428226 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428226
  have eq428313 : (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq428274
       have r₂ := eq67168
       grind)
    | exact resolve eq428274 eq67168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67168 eq428274
  have eq428339 : (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq428313
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq428313
    | exact resolve eq428313 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428313
  have eq428340 : (σ x) = (σ y) ∨ (σ (k x x)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq428339
  have eq428348 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq428340
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq428340
    | exact resolve eq428340 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428340
  have eq428355 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq428348
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq428348
    | exact resolve eq428348 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428348
  have eq428360 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq428355
    | exact resolve eq428355 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428355
  have eq428361 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq428360
  have eq428366 : (M.op (σ x) (σ y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq428361
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq428361
    | exact resolve eq428361 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428361
  have eq428370 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq428366
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq428366
    | exact resolve eq428366 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428366
  have eq428371 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq428370
  have eq428374 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) := by
    first
    | (have r₁ := eq428371
       have r₂ := eq428232
       grind)
    | exact resolve eq428371 eq428232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428232 eq428371
  have eq428420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq428374 eq51263
    | exact resolve eq51263 eq428374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428374
  have eq428918 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y y) := by grind
  clear eq428420
  have eq428957 : (M.op x y) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq428918
       have r₂ := eq28
       grind)
    | exact resolve eq428918 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428918
  have eq428963 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61
       have i₂ := eq428957
       grind)
    | exact superpose eq428957 eq61
    | (have r₁ := eq61
       have r₂ := eq428957
       grind)
    | exact resolve eq61 eq428957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq428964 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq428957
       grind)
    | exact superpose eq428957 eq74
    | exact resolve eq74 eq428957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq428957
  have eq429101 : (M.op x y) ≠ (M.op x y) ∨ (k x x) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq428963
  have eq429102 : (k x x) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq429101
  have eq429153 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq428964
    | exact resolve eq428964 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428964
  have eq429259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq429153 eq97
    | exact resolve eq97 eq429153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq429153
  have eq429428 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq429259
  have eq429451 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq429428
       have r₂ := eq28
       grind)
    | exact resolve eq429428 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429428
  have eq429464 : (σ (k x x)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq429102
       grind)
    | exact superpose eq429102 eq73
    | exact resolve eq73 eq429102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq429102
  have eq429615 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq429464
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq429464
    | exact resolve eq429464 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq429464
  have eq432458 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq429451 eq429615
    | exact resolve eq429615 eq429451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429451 eq429615
  have eq432471 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq432458
  have eq433562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq432471 eq51263
    | exact resolve eq51263 eq432471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51263 eq432471
  have eq434062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq433562
  have eq434089 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq434062
       have r₂ := eq28
       grind)
    | exact resolve eq434062 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434062
  have eq434092 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq434089 eq30
    | exact resolve eq30 eq434089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq434089
  have eq434299 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq434092
    | exact resolve eq434092 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq434092
  have eq434300 : x = y := by grind
  clear eq434299
  have eq434302 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq434300
       grind)
    | exact superpose eq434300 eq19
    | exact resolve eq19 eq434300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq434303 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq434300
       grind)
    | exact superpose eq434300 eq25
    | exact resolve eq25 eq434300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq434300
  have eq434713 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq434303
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq434303
    | exact resolve eq434303 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq434303
  have eq434714 : (M.op x y) = (k x x) := by grind
  clear eq434302
  have eq434715 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq434713 eq27
    | exact resolve eq27 eq434713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq434713
  have eq434978 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq434715
  have eq435300 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq434978 eq52
    | exact resolve eq52 eq434978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq434978
  have eq435639 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq435300
       have i₂ := eq434714
       grind)
    | exact superpose eq434714 eq435300
    | exact resolve eq435300 eq434714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434714 eq435300
  have eq435684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq435639 eq15
    | exact resolve eq15 eq435639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435639
  have eq436176 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq435684
    | exact resolve eq435684 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq435684
  have eq436314 : False := by grind
  exact eq436314

/-- `x □ y = if X = Y then m(X,X) else if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_x_pyy_y_pxx_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq25 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq20
    | (have j0 := eq20 (σ X0) X1
       grind)
    | exact resolve eq20 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq20 X0 X1
       grind)
    | (have r₁ := eq34 X0 X1
       have r₂ := eq20 X0 X1
       grind)
    | (have r₁ := eq34 (k X0 X0) X0
       have r₂ := eq20 X0 X1
       grind)
    | (have r₁ := eq34 X0 (k X0 X0)
       have r₂ := eq20 X0 X1
       grind)
    | exact resolve eq34 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq36 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq35
  have eq45 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq36
    | (have j0 := eq36 (σ X0) X1
       grind)
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) = X0 ∨ X0 = X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    grind
  clear eq58
  have eq72 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59 (σ y) (σ x)
       grind)
    | exact superpose eq59 eq16
    | (have j1 := eq59 (σ y) (σ x)
       grind)
    | (have r₁ := eq16
       have r₂ := eq59 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq59 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq72
    | exact resolve eq72 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq74 : (σ y) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq73
    | exact resolve eq73 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq74
    | exact resolve eq74 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq76 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq75
    | (have j1 := eq59 y x
       grind)
    | (have r₁ := eq75
       have r₂ := eq59 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq75
       have r₂ := eq59 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq75 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq75
  have eq77 : x = y ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ x = (k x x) := by grind
  clear eq76
  have eq194 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq195 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ x = (k x x) := by grind
  clear eq194
  have eq196 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ x = (k x x) := by grind
  clear eq195
  have eq197 : x = (k x x) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have r₁ := eq196
       have r₂ := eq15 x x
       grind)
    | exact resolve eq196 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq609 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq25 x X0
       have i₂ := eq197
       grind)
    | exact superpose eq197 eq25
    | (have j0 := eq25 x X0
       grind)
    | (have r₁ := eq25 y x
       have r₂ := eq197
       grind)
    | (have r₁ := eq25 x x
       have r₂ := eq197
       grind)
    | exact resolve eq25 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (k x X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq20 x X0
       have i₂ := eq197
       grind)
    | exact superpose eq197 eq20
    | (have j0 := eq20 x X0
       grind)
    | (have r₁ := eq20 x x
       have r₂ := eq197
       grind)
    | (have r₁ := eq20 y x
       have r₂ := eq197
       grind)
    | exact resolve eq20 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq612 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = X0 ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq611 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq614 : ∀ X0 : G, (σ x) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq609 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq618 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = X0 ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have j0 := eq614 X0
       have j1 := eq25 x X0
       grind)
    | (have r₁ := eq614 (σ (k x x))
       have r₂ := eq25 x x
       grind)
    | (have r₁ := eq614 X0
       have r₂ := eq25 y x
       grind)
    | (have r₁ := eq614 X0
       have r₂ := eq25 x x
       grind)
    | exact resolve eq614 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq614
  have eq5925 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq618 (σ y)
       grind)
    | exact superpose eq618 eq16
    | (have j1 := eq618 (σ y)
       grind)
    | exact resolve eq16 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq5928 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq5925
  have eq5931 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq5928
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq5928
    | exact resolve eq5928 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5928
  have eq5942 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq5931
       have i₂ := eq612 y
       grind)
    | exact superpose eq612 eq5931
    | (have j1 := eq612 y
       grind)
    | exact resolve eq5931 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq5947 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ x = y ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5942
  have eq5948 : x = y ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5947
  have eq5950 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5948
       grind)
    | exact superpose eq5948 eq16
    | exact resolve eq16 eq5948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5948
  have eq5951 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5950
  have eq5952 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5951
  have eq5953 : y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have r₁ := eq5952
       have r₂ := eq15 x x
       grind)
    | exact resolve eq5952 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5952
  have eq5960 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (k X0 y) = (M.op X0 y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 y
       have i₂ := eq5953
       grind)
    | exact superpose eq5953 eq36
    | (have j0 := eq36 y X0
       grind)
    | (have r₁ := eq36 X0 y
       have r₂ := eq5953
       grind)
    | exact resolve eq36 eq5953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5961 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq45 y X0
       have i₂ := eq5953
       grind)
    | exact superpose eq5953 eq45
    | (have j0 := eq45 y X0
       grind)
    | (have r₁ := eq45 y x
       have r₂ := eq5953
       grind)
    | (have r₁ := eq45 x x
       have r₂ := eq5953
       grind)
    | exact resolve eq45 eq5953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5953
  have eq5978 : ∀ X0 : G, (σ y) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq5961 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5961
  have eq5979 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = X0 ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq5960 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5960
  have eq5982 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq5978 X0
       have j1 := eq45 y X0
       grind)
    | (have r₁ := eq5978 (σ (k y y))
       have r₂ := eq45 y x
       grind)
    | (have r₁ := eq5978 X0
       have r₂ := eq45 y x
       grind)
    | (have r₁ := eq5978 X0
       have r₂ := eq45 x x
       grind)
    | exact resolve eq5978 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5978
  have eq5985 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5982 (σ x)
       grind)
    | exact superpose eq5982 eq16
    | (have j1 := eq5982 (σ x)
       grind)
    | exact resolve eq16 eq5982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5982
  have eq5988 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5985
  have eq5991 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq5988
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq5988
    | exact resolve eq5988 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5988
  have eq6005 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) ∨ x = y ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq5991
       have i₂ := eq5979 x
       grind)
    | exact superpose eq5979 eq5991
    | (have j1 := eq5979 x
       grind)
    | exact resolve eq5991 eq5979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5979 eq5991
  have eq6011 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) ∨ x = y ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6005
  have eq6012 : x = y ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6011
  have eq6059 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6012
       grind)
    | exact superpose eq6012 eq16
    | exact resolve eq16 eq6012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6012
  have eq6060 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6059
  have eq6061 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6060
  have eq6062 : (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq6061
       have r₂ := eq15 x x
       grind)
    | exact resolve eq6061 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6061
  have eq6108 : y = (τ (σ x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq6062
       grind)
    | exact superpose eq6062 eq9
    | exact resolve eq9 eq6062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6062
  have eq6197 : x = y ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq6108
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq6108
    | exact resolve eq6108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6108
  have eq6201 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6197
       grind)
    | exact superpose eq6197 eq16
    | exact resolve eq16 eq6197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6197
  have eq6202 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6201
  have eq6203 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6202
  have eq6204 : (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq6203
       have r₂ := eq15 x x
       grind)
    | exact resolve eq6203 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6203
  have eq6479 : (k x x) = (τ (σ x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq6204
       grind)
    | exact superpose eq6204 eq9
    | exact resolve eq9 eq6204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6204
  have eq6582 : x = (k x x) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq6479
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq6479
    | exact resolve eq6479 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6479
  have eq6584 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (k x X0) = (M.op x X0) ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq20 x X0
       have i₂ := eq6582
       grind)
    | exact superpose eq6582 eq20
    | (have j0 := eq20 x X0
       grind)
    | (have r₁ := eq20 x x
       have r₂ := eq6582
       grind)
    | exact resolve eq20 eq6582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6582
  have eq6611 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = X0 ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have j0 := eq6584 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6584
  have eq6892 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ x = y ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq5931
       have i₂ := eq6611 y
       grind)
    | exact superpose eq6611 eq5931
    | (have j1 := eq6611 y
       grind)
    | exact resolve eq5931 eq6611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5931
  have eq6897 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ x = y := by grind
  clear eq6892
  have eq6898 : x = y ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq6897
  have eq12533 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6898
       grind)
    | exact superpose eq6898 eq16
    | exact resolve eq16 eq6898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6898
  have eq12546 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq12533
  have eq12547 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq12546
  have eq12548 : y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12547
       have r₂ := eq15 x x
       grind)
    | exact resolve eq12547 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12547
  have eq12913 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq45 y X0
       have i₂ := eq12548
       grind)
    | exact superpose eq12548 eq45
    | (have j0 := eq45 y X0
       grind)
    | (have r₁ := eq45 y x
       have r₂ := eq12548
       grind)
    | exact resolve eq45 eq12548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12548
  have eq12934 : ∀ X0 : G, (σ y) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq12913 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12913
  have eq12938 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq12934 X0
       have j1 := eq45 y X0
       grind)
    | (have r₁ := eq12934 (σ (k y y))
       have r₂ := eq45 y x
       grind)
    | (have r₁ := eq12934 X0
       have r₂ := eq45 y x
       grind)
    | exact resolve eq12934 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq12934
  have eq12942 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12938 (σ x)
       grind)
    | exact superpose eq12938 eq16
    | (have j1 := eq12938 (σ x)
       grind)
    | exact resolve eq16 eq12938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12938
  have eq12943 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq12942
  have eq12946 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12943
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq12943
    | exact resolve eq12943 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12943
  have eq12949 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq12946
       have i₂ := eq6611 y
       grind)
    | exact superpose eq6611 eq12946
    | (have j1 := eq6611 y
       grind)
    | exact resolve eq12946 eq6611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6611
  have eq12959 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq12949
  have eq12960 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12959
       grind)
    | exact superpose eq12959 eq16
    | exact resolve eq16 eq12959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12959
  have eq12973 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq12960
  have eq12974 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq12973
  have eq12975 : (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq12974
       have r₂ := eq15 x x
       grind)
    | exact resolve eq12974 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12974
  have eq12977 : y = (τ (σ x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq12975
       grind)
    | exact superpose eq12975 eq9
    | exact resolve eq9 eq12975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12975
  have eq13162 : x = y ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq12977
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq12977
    | exact resolve eq12977 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12977
  have eq13165 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13162
       grind)
    | exact superpose eq13162 eq16
    | exact resolve eq16 eq13162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13162
  have eq13178 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq13165
  have eq13179 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq13178
  have eq13180 : (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq13179
       have r₂ := eq15 x x
       grind)
    | exact resolve eq13179 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13179
  have eq13196 : (k y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq13180
       grind)
    | exact superpose eq13180 eq9
    | exact resolve eq9 eq13180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13180
  have eq13393 : y = (k y y) := by
    first
    | (have i₁ := eq13196
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq13196
    | exact resolve eq13196 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13196
  have eq13403 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq36 X0 y
       have i₂ := eq13393
       grind)
    | exact superpose eq13393 eq36
    | (have j0 := eq36 y X0
       grind)
    | (have r₁ := eq36 X0 y
       have r₂ := eq13393
       grind)
    | exact resolve eq36 eq13393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq13393
  have eq13426 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq13403 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13403
  have eq13439 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12946
       have i₂ := eq13426 x
       grind)
    | exact superpose eq13426 eq12946
    | (have j1 := eq13426 x
       grind)
    | exact resolve eq12946 eq13426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12946 eq13426
  have eq13445 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq13439
  have eq13448 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13445
       grind)
    | exact superpose eq13445 eq16
    | exact resolve eq16 eq13445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13445
  have eq13464 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq13448
  have eq13465 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq13464
  have eq13466 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq13465
       have r₂ := eq15 x x
       grind)
    | exact resolve eq13465 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13465
  have eq13468 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq13466
       grind)
    | exact superpose eq13466 eq9
    | exact resolve eq9 eq13466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13466
  have eq13653 : x = y := by
    first
    | (have i₁ := eq13468
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq13468
    | exact resolve eq13468 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13468
  have eq13656 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13653
       grind)
    | exact superpose eq13653 eq16
    | exact resolve eq16 eq13653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13653
  have eq13672 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) := by grind
  clear eq13656
  have eq13673 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq13672
  have eq13674 : False := by grind
  exact eq13674
