import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if X = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pyx_pyy_pxx_pyx_pxy_pxx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
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
  clear eq48
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq106 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X0) ∨ (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
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
  have eq27433 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq543 eq97
    | exact resolve eq97 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq27465 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq27433
       have r₂ := eq28
       grind)
    | exact resolve eq27433 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27433
  have eq27488 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq27465 eq80
    | exact resolve eq80 eq27465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27465
  have eq27839 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq27488
       have i₂ := eq672
       grind)
    | exact superpose eq672 eq27488
    | exact resolve eq27488 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27488
  have eq27868 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq27839
  have eq28548 : (k (σ x) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq27868
       grind)
    | exact superpose eq27868 eq44
    | exact resolve eq44 eq27868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27868
  have eq28620 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq28548
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq28548
    | exact resolve eq28548 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28548
  have eq28621 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq28620
  have eq28657 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq28621 eq62
    | (have r₁ := eq62
       have r₂ := eq28621
       grind)
    | exact resolve eq62 eq28621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28621
  have eq28680 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq28657
  have eq28681 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq28680
  have eq29047 : (k y y) = (τ (k (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq28681 eq85
    | exact resolve eq85 eq28681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28681
  have eq29085 : (k y x) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq80 eq29047
    | exact resolve eq29047 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29047
  have eq29088 : (k y x) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq29085
       have r₂ := eq61
       grind)
    | exact resolve eq29085 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29085
  have eq29346 : (k (σ y) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq29088
       grind)
    | exact superpose eq29088 eq74
    | exact resolve eq74 eq29088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29349 : (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq29088
       grind)
    | exact superpose eq29088 eq96
    | exact resolve eq96 eq29088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq29088
  have eq29388 : (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq29349
  have eq29415 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq29346
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq29346
    | exact resolve eq29346 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29346
  have eq29436 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq29388
       grind)
    | exact superpose eq29388 eq73
    | exact resolve eq73 eq29388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq29486 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq29436
    | exact resolve eq29436 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29436
  have eq29777 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29486 eq708
    | exact resolve eq708 eq29486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29486
  have eq29783 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq29777
  have eq29788 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq29783
       have r₂ := eq28
       grind)
    | exact resolve eq29783 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29783
  have eq29805 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq29415 eq97
    | exact resolve eq97 eq29415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq29806 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq29415 eq131
    | exact resolve eq131 eq29415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq29415
  have eq29831 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq29806
  have eq29832 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq29805
  have eq29841 : (k (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq29831
       have r₂ := eq708
       grind)
    | exact resolve eq29831 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708 eq29831
  have eq32159 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq29788 eq62
    | (have r₁ := eq62
       have r₂ := eq29788
       grind)
    | exact resolve eq62 eq29788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq29788
  have eq32185 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq32159
  have eq32186 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq32185
  have eq48101 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq29841 eq29832
    | exact resolve eq29832 eq29841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29832 eq29841
  have eq48135 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq48101
  have eq59356 : (k y y) = (τ (k (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq32186 eq85
    | exact resolve eq85 eq32186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32186
  have eq59394 : (k y x) = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq80 eq59356
    | exact resolve eq59356 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq59356
  have eq59397 : (k y x) = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq59394
       have r₂ := eq61
       grind)
    | exact resolve eq59394 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59394
  have eq59706 : (M.op x y) ≠ (k y x) ∨ (k x x) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq130
       have i₂ := eq59397
       grind)
    | exact superpose eq59397 eq130
    | exact resolve eq130 eq59397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq59397
  have eq59742 : (M.op x y) ≠ (k y x) ∨ (k x x) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq59706
  have eq59767 : (k x x) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq59742
       have r₂ := eq672
       grind)
    | exact resolve eq59742 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq59742
  have eq62155 : (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq29388
       have i₂ := eq59767
       grind)
    | exact superpose eq59767 eq29388
    | exact resolve eq29388 eq59767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29388 eq59767
  have eq62206 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by grind
  clear eq62155
  have eq62267 : (τ (σ (M.op x y))) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq62206 eq52
    | exact resolve eq52 eq62206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62206
  have eq62361 : (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq31 eq62267
    | exact resolve eq62267 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq62267
  have eq62362 : (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq62361
  have eq62370 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq62362
       grind)
    | exact superpose eq62362 eq44
    | exact resolve eq44 eq62362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq62372 : (M.op x y) ≠ (M.op x y) ∨ (k y x) = (k y y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61
       have i₂ := eq62362
       grind)
    | exact superpose eq62362 eq61
    | (have r₁ := eq61
       have r₂ := eq62362
       grind)
    | exact resolve eq61 eq62362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq62362
  have eq62436 : (M.op x y) ≠ (M.op x y) ∨ (k y x) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq62372
  have eq62437 : (k y x) = (k y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq62436
  have eq62468 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq62370
    | exact resolve eq62370 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62370
  have eq62503 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq62468 eq48135
    | exact resolve eq48135 eq62468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48135
  have eq62570 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq62503
  have eq62580 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq62570
       have r₂ := eq28
       grind)
    | exact resolve eq62570 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62570
  have eq62905 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (k y y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq911 y
       have i₂ := eq62580
       grind)
    | exact superpose eq62580 eq911
    | (have j0 := eq911 y
       grind)
    | exact resolve eq911 eq62580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq62919 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ (k y y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq62905
    | exact resolve eq62905 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62905
  have eq62942 : (σ (k y y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq62919
       have r₂ := eq62468
       grind)
    | exact resolve eq62919 eq62468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62468 eq62919
  have eq62944 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq62942
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq62942
    | exact resolve eq62942 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62942
  have eq62946 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq62944
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq62944
    | exact resolve eq62944 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq62944
  have eq62948 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq62946
    | exact resolve eq62946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62946
  have eq62950 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq62948
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq62948
    | exact resolve eq62948 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62948
  have eq62951 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq62950
  have eq62953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq62951
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq62951
    | exact resolve eq62951 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62951
  have eq62955 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq62953
    | exact resolve eq62953 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62953
  have eq62958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq62955
    | exact resolve eq62955 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62955
  have eq62960 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq62958
       have r₂ := eq28
       grind)
    | exact resolve eq62958 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62958
  have eq63279 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq62960 eq85
    | exact resolve eq85 eq62960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq62960
  have eq63766 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq63279
       have i₂ := eq62437
       grind)
    | exact superpose eq62437 eq63279
    | exact resolve eq63279 eq62437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62437 eq63279
  have eq63785 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq63766
  have eq63882 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq62580
       have i₂ := eq63785
       grind)
    | exact superpose eq63785 eq62580
    | exact resolve eq62580 eq63785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62580 eq63785
  have eq63887 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq63882
  have eq64245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq63887 eq15
    | exact resolve eq15 eq63887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63887
  have eq64403 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq64245
    | exact resolve eq64245 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64245
  have eq64404 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq64403
       have r₂ := eq28
       grind)
    | exact resolve eq64403 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64403
  have eq64406 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq64404 eq30
    | exact resolve eq30 eq64404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq64404
  have eq64527 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq64406
    | exact resolve eq64406 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq64406
  have eq64528 : x = y := by grind
  clear eq64527
  have eq64530 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq64528
       grind)
    | exact superpose eq64528 eq19
    | exact resolve eq19 eq64528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq64531 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq64528
       grind)
    | exact superpose eq64528 eq25
    | exact resolve eq25 eq64528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq64528
  have eq64851 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq64531
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq64531
    | exact resolve eq64531 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq64531
  have eq64852 : (M.op x y) = (k x x) := by grind
  clear eq64530
  have eq64855 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq64851 eq27
    | exact resolve eq27 eq64851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq64851
  have eq64977 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq64855
  have eq65103 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq64977 eq52
    | exact resolve eq52 eq64977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq64977
  have eq65137 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq65103
       have i₂ := eq64852
       grind)
    | exact superpose eq64852 eq65103
    | exact resolve eq65103 eq64852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64852 eq65103
  have eq65153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65137 eq15
    | exact resolve eq15 eq65137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65137
  have eq65363 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq65153
    | exact resolve eq65153 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq65153
  have eq65426 : False := by grind
  exact eq65426

/-- `x □ y = if X = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pyx_pyy_pxx_pyx_pyx_pxx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
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

/-- `x □ y = if X = Y then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pyx_pyy_pxx_pyx_pyy_pxx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
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

/-- `x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pyy_x_pxx_y_pxx_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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

/-- `x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pyy_x_pxx_y_pxx_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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

/-- `x □ y = if X = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pyy_x_pxx_y_pxy_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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

/-- `x □ y = if X = Y then m(X,Y) else if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pyy_x_pxx_y_pxy_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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

/-- `x □ y = if X = Y then m(Y,X) else if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pyy_x_pxx_y_pyx_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
