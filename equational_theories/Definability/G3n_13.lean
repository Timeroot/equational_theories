import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = X then m(Y,X) else if m(X,Y) = Y then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyx_y_pxy_x_pxy_y_pyx_pyx_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq50 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq78 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) := by
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
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq93 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  clear eq44
  have eq109 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq97
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq117 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq146 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
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
  clear eq39
  have eq186 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
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
  have eq609 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq91 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq91 X1 X1
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq616 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq609 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq619 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq616 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq616 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq616 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq616 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq616 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq629 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq630 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  clear eq49
  have eq3673 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq186 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq4275 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (k (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq93 eq12
    | (have j0 := eq12 (σ y) (σ X0)
       have j1 := eq93 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ y)
       have r₂ := eq93 y
       grind)
    | (have r₁ := eq12 (σ y) (σ X0)
       have r₂ := eq93 X0
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq4280 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (k (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4275 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4275
  have eq4284 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (k (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4280 X0
       have j1 := eq12 (σ y) (σ X0)
       grind)
    | (have r₁ := eq4280 y
       have r₂ := eq12 (σ y) (σ y)
       grind)
    | (have r₁ := eq4280 X0
       have r₂ := eq12 (σ y) (σ X0)
       grind)
    | exact resolve eq4280 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4280
  have eq4322 : ∀ X0 : G, (σ y) = (σ (k y X0)) ∨ (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq4284
    | (have j0 := eq4284 X0
       grind)
    | exact resolve eq4284 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq4284
  have eq4323 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4322 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4322
  have eq10807 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3545 eq109
    | exact resolve eq109 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq3545
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
    | exact superpose eq3552 eq14181
    | exact resolve eq14181 eq3552
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
  have eq22044 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22045 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq22044
    | exact resolve eq22044 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22044
  have eq22056 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq22045
       have r₂ := eq27
       grind)
    | exact resolve eq22045 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22045
  have eq22060 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq22056
    | exact resolve eq22056 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22056
  have eq22062 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq22060
    | exact resolve eq22060 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22060
  have eq22065 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq22066 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq22065
  have eq22149 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq22066 eq55
    | exact resolve eq55 eq22066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22066
  have eq22178 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq22149
    | exact resolve eq22149 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22149
  have eq24803 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq24804 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq24803
  have eq24808 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24804
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24804
    | exact resolve eq24804 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24804
  have eq24809 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24808
  have eq24825 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24809
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24809
    | exact resolve eq24809 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24809
  have eq24826 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24825
  have eq25157 : y ≠ y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq24826
       grind)
    | exact superpose eq24826 eq56
    | (have j0 := eq56 y x
       grind)
    | (have r₁ := eq56 y x
       have r₂ := eq24826
       grind)
    | (have r₁ := eq56 x y
       have r₂ := eq24826
       grind)
    | (have r₁ := eq56 (σ x) (σ y)
       have r₂ := eq24826
       grind)
    | exact resolve eq56 eq24826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25158 : y ≠ y ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq24826
       grind)
    | exact superpose eq24826 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq24826
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq24826
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq24826
       grind)
    | exact resolve eq14 eq24826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24826
  have eq25159 : y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25158
  have eq25160 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25157
  have eq25161 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25160
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25160
    | exact resolve eq25160 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25160
  have eq25162 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq25161
       have r₂ := eq50
       grind)
    | exact resolve eq25161 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25161
  have eq25166 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq25162
       grind)
    | exact superpose eq25162 eq70
    | exact resolve eq70 eq25162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25162
  have eq25203 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq25166
    | exact resolve eq25166 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25166
  have eq25611 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq613 x y
       have i₂ := eq25159
       grind)
    | exact superpose eq25159 eq613
    | (have j0 := eq613 x y
       grind)
    | exact resolve eq613 eq25159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25159
  have eq25618 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25611
  have eq25623 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25618
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25618
    | exact resolve eq25618 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25618
  have eq25636 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25623
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25623
    | exact resolve eq25623 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25623
  have eq25642 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq25636
    | exact resolve eq25636 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25636
  have eq25643 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25642
  have eq25647 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25643
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25643
    | exact resolve eq25643 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25643
  have eq25652 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25647
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25647
    | exact resolve eq25647 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25647
  have eq25656 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq25652
    | exact resolve eq25652 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25652
  have eq25657 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq25656
  have eq25663 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25657
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25657
    | exact resolve eq25657 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25657
  have eq25666 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25663
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25663
    | exact resolve eq25663 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25663
  have eq26021 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25666 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | (have r₁ := eq56 (σ y) (σ x)
       have r₂ := eq25666
       grind)
    | (have r₁ := eq56 (σ x) (σ y)
       have r₂ := eq25666
       grind)
    | (have r₁ := eq56 x y
       have r₂ := eq25666
       grind)
    | exact resolve eq56 eq25666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25666
  have eq26024 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq26021
  have eq26025 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq26024
    | exact resolve eq26024 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26024
  have eq26026 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26025
       have r₂ := eq51
       grind)
    | exact resolve eq26025 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26025
  have eq26046 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26026 eq25203
    | exact resolve eq25203 eq26026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25203 eq26026
  have eq26053 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26046
  have eq26064 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26053
       have r₂ := eq27
       grind)
    | exact resolve eq26053 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26053
  have eq26367 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26064 eq79
    | (have r₁ := eq79
       have r₂ := eq26064
       grind)
    | exact resolve eq79 eq26064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq26370 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26064 eq27
    | exact resolve eq27 eq26064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26371 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq26064
  have eq26372 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq26367
  have eq66976 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26372
       have r₂ := eq26371
       grind)
    | exact resolve eq26372 eq26371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26372
  have eq66980 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66976 eq14
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq66976
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq66976
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq66976
       grind)
    | exact resolve eq14 eq66976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66976
  have eq66981 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq66980
  have eq67287 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66981 eq118
    | exact resolve eq118 eq66981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq66981
  have eq67310 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq67287
  have eq67320 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq67310
       have r₂ := eq26370
       grind)
    | exact resolve eq67310 eq26370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26370 eq67310
  have eq84710 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq67320 eq55
    | exact resolve eq55 eq67320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67320
  have eq84764 : x = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq84710
    | exact resolve eq84710 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84710
  have eq84773 : y = (M.op y x) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq84764
       have r₂ := eq78
       grind)
    | exact resolve eq84764 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq84764
  have eq84775 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq84773
       grind)
    | exact superpose eq84773 eq56
    | (have j0 := eq56 y x
       grind)
    | (have r₁ := eq56 y x
       have r₂ := eq84773
       grind)
    | (have r₁ := eq56 x y
       have r₂ := eq84773
       grind)
    | (have r₁ := eq56 (σ x) (σ y)
       have r₂ := eq84773
       grind)
    | exact resolve eq56 eq84773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84776 : y ≠ y ∨ y = (k x y) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq84773
       grind)
    | exact superpose eq84773 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq84773
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq84773
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq84773
       grind)
    | exact resolve eq14 eq84773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84773
  have eq84777 : y = (k x y) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq84776
  have eq84778 : (M.op x y) = (k y x) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq84775
  have eq84779 : (M.op x y) = (k y x) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq84778
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84778
    | exact resolve eq84778 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84778
  have eq84780 : (M.op x y) = (k y x) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq84779
       have r₂ := eq50
       grind)
    | exact resolve eq84779 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84779
  have eq85180 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq84780
       grind)
    | exact superpose eq84780 eq70
    | exact resolve eq70 eq84780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84780
  have eq85267 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq85180
    | exact resolve eq85180 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85180
  have eq85425 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq84777
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq84777
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq84777 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85439 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq613 x y
       have i₂ := eq84777
       grind)
    | exact superpose eq84777 eq613
    | (have j0 := eq613 x y
       grind)
    | exact resolve eq613 eq84777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq84777
  have eq85447 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq85439
  have eq85448 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq85425
  have eq85453 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85447
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq85447
    | exact resolve eq85447 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85447
  have eq85467 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq85448
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85448
    | exact resolve eq85448 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85448
  have eq85471 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85453
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85453
    | exact resolve eq85453 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85453
  have eq85474 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq85467
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85467
    | exact resolve eq85467 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85467
  have eq85475 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq85474
  have eq85479 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq85471
    | exact resolve eq85471 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85471
  have eq85480 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq85479
  have eq85484 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85480
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq85480
    | exact resolve eq85480 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85480
  have eq85489 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85484
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85484
    | exact resolve eq85484 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85484
  have eq85493 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq85489
    | exact resolve eq85489 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85489
  have eq85498 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85493
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85493
    | exact resolve eq85493 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85493
  have eq85500 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85498
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq85498
    | exact resolve eq85498 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85498
  have eq85895 : y ≠ y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq85475
       grind)
    | exact superpose eq85475 eq56
    | (have j0 := eq56 y x
       grind)
    | (have r₁ := eq56 y x
       have r₂ := eq85475
       grind)
    | (have r₁ := eq56 (σ x) (σ y)
       have r₂ := eq85475
       grind)
    | (have r₁ := eq56 x y
       have r₂ := eq85475
       grind)
    | exact resolve eq56 eq85475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85896 : y ≠ y ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq85475
       grind)
    | exact superpose eq85475 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq85475
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq85475
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq85475
       grind)
    | exact resolve eq14 eq85475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85475
  have eq85897 : y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq85896
  have eq85898 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq85895
  have eq85899 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85898
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85898
    | exact resolve eq85898 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85898
  have eq85900 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq85899
       have r₂ := eq50
       grind)
    | exact resolve eq85899 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85899
  have eq85908 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq85900
       grind)
    | exact superpose eq85900 eq70
    | exact resolve eq70 eq85900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85900
  have eq86029 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq85908
    | exact resolve eq85908 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85908
  have eq86651 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq630 x y
       have i₂ := eq85897
       grind)
    | exact superpose eq85897 eq630
    | (have j0 := eq630 x y
       grind)
    | exact resolve eq630 eq85897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630 eq85897
  have eq86655 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq86651
  have eq86659 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86655
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq86655
    | exact resolve eq86655 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86655
  have eq86676 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86659
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86659
    | exact resolve eq86659 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86659
  have eq86681 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq86676
       have r₂ := eq26371
       grind)
    | exact resolve eq86676 eq26371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26371 eq86676
  have eq86684 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86681
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86681
    | exact resolve eq86681 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86681
  have eq86686 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86684
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq86684
    | exact resolve eq86684 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86684
  have eq86688 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86686
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq86686
    | exact resolve eq86686 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86686
  have eq86690 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86688
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86688
    | exact resolve eq86688 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86688
  have eq86691 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq86690
    | exact resolve eq86690 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86690
  have eq86692 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq86691
  have eq87147 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq86692 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | (have r₁ := eq56 (σ y) (σ x)
       have r₂ := eq86692
       grind)
    | (have r₁ := eq56 (σ x) (σ y)
       have r₂ := eq86692
       grind)
    | (have r₁ := eq56 x y
       have r₂ := eq86692
       grind)
    | exact resolve eq56 eq86692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86692
  have eq87150 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq87147
  have eq87152 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq87150
    | exact resolve eq87150 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87150
  have eq87153 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq87152
       have r₂ := eq51
       grind)
    | exact resolve eq87152 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87152
  have eq87235 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87153 eq86029
    | exact resolve eq86029 eq87153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86029 eq87153
  have eq87242 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq87235
  have eq87310 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq87242
       have r₂ := eq27
       grind)
    | exact resolve eq87242 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87242
  have eq87715 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87310 eq51
    | (have r₁ := eq51
       have r₂ := eq87310
       grind)
    | exact resolve eq51 eq87310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87310
  have eq87772 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq87715
  have eq88212 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87772 eq77
    | exact resolve eq77 eq87772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87772
  have eq88454 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq88212
    | exact resolve eq88212 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88212
  have eq88571 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq88454
       grind)
    | exact superpose eq88454 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq88454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88572 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq88571
  have eq88664 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88572
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88572
    | exact resolve eq88572 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88572
  have eq88665 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq88664
  have eq141806 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq88665
       grind)
    | exact superpose eq88665 eq56
    | (have j0 := eq56 y x
       grind)
    | (have r₁ := eq56 y x
       have r₂ := eq88665
       grind)
    | (have r₁ := eq56 x y
       have r₂ := eq88665
       grind)
    | exact resolve eq56 eq88665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88665
  have eq141810 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq141806
  have eq141811 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq141810
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq141810
    | exact resolve eq141810 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141810
  have eq141812 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq141811
       have r₂ := eq50
       grind)
    | exact resolve eq141811 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141811
  have eq142741 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq88454
       have i₂ := eq141812
       grind)
    | exact superpose eq141812 eq88454
    | exact resolve eq88454 eq141812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141812
  have eq142752 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq142741
  have eq142897 : x ≠ x ∨ x = y ∨ x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq142752
       grind)
    | exact superpose eq142752 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq142752
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq142752
       grind)
    | exact resolve eq12 eq142752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142752
  have eq142900 : x = y ∨ x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq142897
  have eq142913 : x = (M.op x y) ∨ x = y ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq142900
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq142900
    | exact resolve eq142900 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142900
  have eq142914 : y = (k y x) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq142913
  have eq144305 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq88454
       have i₂ := eq142914
       grind)
    | exact superpose eq142914 eq88454
    | exact resolve eq88454 eq142914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88454 eq142914
  have eq144319 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq144305
  have eq144490 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq144319 eq20
    | exact resolve eq20 eq144319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144319
  have eq144774 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq144490
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq144490
    | exact resolve eq144490 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144490
  have eq1411985 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq85500 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | (have r₁ := eq56 (σ y) (σ x)
       have r₂ := eq85500
       grind)
    | (have r₁ := eq56 (σ x) (σ y)
       have r₂ := eq85500
       grind)
    | (have r₁ := eq56 x y
       have r₂ := eq85500
       grind)
    | exact resolve eq56 eq85500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85500
  have eq1411986 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq1411985
  have eq1412040 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1411986
    | exact resolve eq1411986 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411986
  have eq1412046 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1412040
       have r₂ := eq51
       grind)
    | exact resolve eq1412040 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412040
  have eq1412175 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1412046 eq85267
    | exact resolve eq85267 eq1412046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85267 eq1412046
  have eq1412518 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1412175
  have eq1412602 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1412518
       have r₂ := eq27
       grind)
    | exact resolve eq1412518 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412518
  have eq1412740 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3673 x
       have i₂ := eq1412602
       grind)
    | exact superpose eq1412602 eq3673
    | (have j0 := eq3673 x
       grind)
    | exact resolve eq3673 eq1412602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3673
  have eq1412773 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1412740
  have eq1412851 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1412773
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1412773
    | exact resolve eq1412773 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412773
  have eq1412954 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1412851
    | exact resolve eq1412851 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412851
  have eq1412955 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1412954
  have eq1412998 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1412955
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1412955
    | exact resolve eq1412955 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412955
  have eq1413018 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1412998
    | exact resolve eq1412998 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412998
  have eq1413019 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1413018
  have eq1413036 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1413019
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1413019
    | exact resolve eq1413019 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413019
  have eq1438957 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1413036 eq14
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq1413036
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq1413036
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq1413036
       grind)
    | exact resolve eq14 eq1413036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413036
  have eq1438960 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1438957
  have eq1442156 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1438960 eq55
    | exact resolve eq55 eq1438960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1438960
  have eq1442511 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1442156
    | exact resolve eq1442156 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442156
  have eq1442708 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1412602
       have i₂ := eq1442511
       grind)
    | exact superpose eq1442511 eq1412602
    | exact resolve eq1412602 eq1442511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412602 eq1442511
  have eq1442755 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1442708
  have eq1443102 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1442755 eq27
    | exact resolve eq27 eq1442755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442755
  have eq1444512 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1443102
       have r₂ := eq144774
       grind)
    | exact resolve eq1443102 eq144774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144774 eq1443102
  have eq1444521 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1444512 eq51
    | (have r₁ := eq51
       have r₂ := eq1444512
       grind)
    | exact resolve eq51 eq1444512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444512
  have eq1445624 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1444521
  have eq1445683 : (τ (σ x)) = (k y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1445624 eq77
    | exact resolve eq77 eq1445624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445624
  have eq1446369 : x = (k y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq1445683
    | exact resolve eq1445683 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445683
  have eq1446744 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq1446369
       grind)
    | exact superpose eq1446369 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1446369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1446758 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1446744
  have eq1446936 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1446758
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1446758
    | exact resolve eq1446758 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446758
  have eq1446937 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1446936
  have eq1993063 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq1446937
       grind)
    | exact superpose eq1446937 eq56
    | (have j0 := eq56 y x
       grind)
    | (have r₁ := eq56 y x
       have r₂ := eq1446937
       grind)
    | (have r₁ := eq56 x y
       have r₂ := eq1446937
       grind)
    | exact resolve eq56 eq1446937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446937
  have eq1993065 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1993063
  have eq1993068 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1993065
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1993065
    | exact resolve eq1993065 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993065
  have eq1993069 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq1993068
       have r₂ := eq50
       grind)
    | exact resolve eq1993068 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993068
  have eq1993359 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1446369
       have i₂ := eq1993069
       grind)
    | exact superpose eq1993069 eq1446369
    | exact resolve eq1446369 eq1993069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993069
  have eq1993430 : x = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1993359
  have eq1993790 : x ≠ x ∨ x = y ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1993430
       grind)
    | exact superpose eq1993430 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1993430
       grind)
    | exact resolve eq12 eq1993430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993430
  have eq1993793 : x ≠ x ∨ x = y ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq1993790
  have eq1993794 : x = y ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq1993793
  have eq1993809 : x = (M.op x y) ∨ x = y ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1993794
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1993794
    | exact resolve eq1993794 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993794
  have eq1993810 : y = (k y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1993809
  have eq1994178 : x = y ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1446369
       have i₂ := eq1993810
       grind)
    | exact superpose eq1993810 eq1446369
    | exact resolve eq1446369 eq1993810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446369 eq1993810
  have eq1994253 : x = (M.op x y) ∨ x = y := by grind
  clear eq1994178
  have eq1994674 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1994253 eq20
    | exact resolve eq20 eq1994253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1994676 : x ≠ x ∨ x = (k y x) ∨ x = y := by
    first
    | exact superpose eq1994253 eq50
    | (have r₁ := eq50
       have r₂ := eq1994253
       grind)
    | exact resolve eq50 eq1994253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1994253
  have eq1995332 : x = (k y x) ∨ x = y := by grind
  clear eq1994676
  have eq1995895 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1994674
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1994674
    | exact resolve eq1994674 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994674
  have eq1996087 : (k y x) = (τ (k (σ y) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq1995895 eq77
    | exact resolve eq77 eq1995895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1998007 : (k y x) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq89 eq1996087
    | exact resolve eq1996087 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996087
  have eq1998188 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq70
       have i₂ := eq1995332
       grind)
    | exact superpose eq1995332 eq70
    | exact resolve eq70 eq1995332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1998518 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq4323 x
       have i₂ := eq1995332
       grind)
    | exact superpose eq1995332 eq4323
    | (have j0 := eq4323 x
       grind)
    | exact resolve eq4323 eq1995332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4323 eq1995332
  have eq1998546 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq1998518
  have eq1998611 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1998546
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1998546
    | exact resolve eq1998546 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998546
  have eq1998715 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1998188
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1998188
    | exact resolve eq1998188 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998188
  have eq1998731 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1998611
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1998611
    | exact resolve eq1998611 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998611
  have eq1998774 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq1998731
    | exact resolve eq1998731 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998731
  have eq1998796 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1998774
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1998774
    | exact resolve eq1998774 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998774
  have eq1998857 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1995895 eq1998715
    | exact resolve eq1998715 eq1995895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1995895 eq1998715
  have eq1999394 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq1998857
  have eq1999493 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1999394 eq89
    | exact resolve eq89 eq1999394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq1999394
  have eq1999764 : (M.op x y) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30 eq1999493
    | exact resolve eq1999493 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1999493
  have eq2005876 : (M.op x y) = (k y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1998007 eq1999764
    | exact resolve eq1999764 eq1998007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998007 eq1999764
  have eq2005950 : (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq2005876
  have eq2006242 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq70
       have i₂ := eq2005950
       grind)
    | exact superpose eq2005950 eq70
    | exact resolve eq70 eq2005950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq2005950
  have eq2006734 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq2006242
    | exact resolve eq2006242 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006242
  have eq2175255 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1998796 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | (have r₁ := eq56 (σ y) (σ x)
       have r₂ := eq1998796
       grind)
    | (have r₁ := eq56 (σ x) (σ y)
       have r₂ := eq1998796
       grind)
    | exact resolve eq56 eq1998796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1998796
  have eq2175256 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2175255
  have eq2175330 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq2175256
    | exact resolve eq2175256 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175256
  have eq2175333 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2175330
       have r₂ := eq51
       grind)
    | exact resolve eq2175330 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2175330
  have eq2175683 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2175333 eq2006734
    | exact resolve eq2006734 eq2175333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006734 eq2175333
  have eq2175787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2175683
  have eq2175890 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2175787
       have r₂ := eq27
       grind)
    | exact resolve eq2175787 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175787
  have eq2175922 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2175890 eq29
    | exact resolve eq29 eq2175890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2175890
  have eq2178660 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq2175922
    | exact resolve eq2175922 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2175922
  have eq2178661 : x = y := by grind
  clear eq2178660
  have eq2178796 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2178661
       grind)
    | exact superpose eq2178661 eq18
    | exact resolve eq18 eq2178661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2178797 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2178661
       grind)
    | exact superpose eq2178661 eq24
    | exact resolve eq24 eq2178661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2178661
  have eq2180810 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2178797
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2178797
    | exact resolve eq2178797 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2178797
  have eq2181005 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2180810 eq26
    | exact resolve eq26 eq2180810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2180810
  have eq2184425 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2181005 eq3552
    | exact resolve eq3552 eq2181005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3552 eq2181005
  have eq2184549 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2184425
       have i₂ := eq14235
       grind)
    | exact superpose eq14235 eq2184425
    | exact resolve eq2184425 eq14235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14235 eq2184425
  have eq2184583 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2184549
       have i₂ := eq2178796
       grind)
    | exact superpose eq2178796 eq2184549
    | exact resolve eq2184549 eq2178796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178796 eq2184549
  have eq2184819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2184583 eq15
    | exact resolve eq15 eq2184583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2184583
  have eq2185632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2184819
    | exact resolve eq2184819 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2184819
  have eq2186110 : False := by grind
  exact eq2186110

/-- `x □ y = if m(Y,X) = Y then Y else if m(X,Y) = X then m(Y,X) else if m(X,Y) = Y then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyx_y_pxy_x_pxy_y_y_pyx_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
  have eq50 : x ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
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
  have eq64 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) := by
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
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  clear eq36
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq100 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  clear eq37
  have eq165 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
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
  have eq225 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq394 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq225 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq225
    | exact resolve eq225 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq225 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq225
    | (have j0 := eq225 X0 y
       grind)
    | exact resolve eq225 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq225
    | (have j0 := eq225 X0 (M.op x y)
       grind)
    | exact resolve eq225 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq643 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq79 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq79 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq79 X1 X1
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq79 X1 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq13 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq650 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq644 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq651 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq643 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq653 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
    | (have r₁ := eq650 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | exact resolve eq650 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq654 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq651 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq651 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq651 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq651 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq651 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq664 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq665 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq666 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq665 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq2971 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (k (σ X0) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
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
  have eq2975 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (k (σ X0) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq2971 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2971
  have eq2979 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (k (σ X0) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq2975 X0
       have j1 := eq13 (σ X0) (σ x)
       grind)
    | (have r₁ := eq2975 X0
       have r₂ := eq13 (σ x) (σ X0)
       grind)
    | (have r₁ := eq2975 X0
       have r₂ := eq13 (σ X0) (σ x)
       grind)
    | (have r₁ := eq2975 x
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq2975 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2975
  have eq3000 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq39 eq2979
    | (have j0 := eq2979 X0
       grind)
    | exact resolve eq2979 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq2979
  have eq5456 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq666 (τ X1) (τ X0)
       have i₂ := eq394 X0 X1
       grind)
    | exact superpose eq394 eq666
    | (have j0 := eq666 (τ X0) (τ X1)
       grind)
    | exact resolve eq666 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq5634 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5456 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq5456
    | (have j0 := eq5456 X0 X1
       grind)
    | exact resolve eq5456 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5456
  have eq5718 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5634 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5634
    | (have j0 := eq5634 X0 X1
       grind)
    | exact resolve eq5634 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5634
  have eq5802 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5718 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq5718
    | (have j0 := eq5718 X0 X1
       grind)
    | exact resolve eq5718 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5718
  have eq5884 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5802 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5802
    | (have j0 := eq5802 X0 X1
       grind)
    | exact resolve eq5802 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5802
  have eq5966 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5884 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5884
    | (have j0 := eq5884 X0 X1
       grind)
    | exact resolve eq5884 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5884
  have eq6048 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5966 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5966
    | (have j0 := eq5966 X0 X1
       grind)
    | exact resolve eq5966 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5966
  have eq6057 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6048 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq6048
    | (have j0 := eq6048 X0 X1
       grind)
    | exact resolve eq6048 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6048
  have eq6064 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6057 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6057
    | (have j0 := eq6057 X0 X1
       grind)
    | exact resolve eq6057 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6057
  have eq6231 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq646 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq646
    | (have j0 := eq646 x y
       grind)
    | exact resolve eq646 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq6300 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6231
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6231
    | exact resolve eq6231 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6231
  have eq6387 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6300
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6300
    | exact resolve eq6300 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6300
  have eq6472 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6387
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6387
    | exact resolve eq6387 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6387
  have eq6556 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq6472
    | exact resolve eq6472 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6472
  have eq6639 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6556
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6556
    | exact resolve eq6556 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6556
  have eq6721 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6639
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6639
    | exact resolve eq6639 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6639
  have eq6803 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq6721
    | exact resolve eq6721 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6721
  have eq6857 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq6803
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6803
    | exact resolve eq6803 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6803
  have eq6865 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6857
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6857
    | exact resolve eq6857 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6857
  have eq7026 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq647 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq647
    | (have j0 := eq647 x y
       grind)
    | exact resolve eq647 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7095 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7026
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7026
    | exact resolve eq7026 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7026
  have eq7182 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7095
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7095
    | exact resolve eq7095 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7095
  have eq7267 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7182
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7182
    | exact resolve eq7182 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7182
  have eq7351 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq7267
    | exact resolve eq7267 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7267
  have eq7434 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7351
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7351
    | exact resolve eq7351 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7351
  have eq7516 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7434
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7434
    | exact resolve eq7434 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7434
  have eq7598 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq7516
    | exact resolve eq7516 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7516
  have eq7652 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq7598
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7598
    | exact resolve eq7598 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7598
  have eq7660 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7652
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7652
    | exact resolve eq7652 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7652
  have eq18318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18318
    | exact resolve eq18318 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18318
  have eq18330 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq18319
       have r₂ := eq27
       grind)
    | exact resolve eq18319 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18319
  have eq18332 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18330
    | exact resolve eq18330 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18330
  have eq18334 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18332
    | exact resolve eq18332 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18332
  have eq18337 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18334 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq18334
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq18334
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq18334
       grind)
    | exact resolve eq14 eq18334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18334
  have eq18338 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq18337
  have eq18347 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18338 eq55
    | exact resolve eq55 eq18338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18338
  have eq18374 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq18347
    | exact resolve eq18347 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18347
  have eq18377 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq18374
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq18374
       have r₂ := eq14 y x
       grind)
    | (have r₁ := eq18374
       have r₂ := eq14 x y
       grind)
    | exact resolve eq18374 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18374
  have eq18394 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq647 x y
       have i₂ := eq18377
       grind)
    | exact superpose eq18377 eq647
    | (have j0 := eq647 x y
       grind)
    | exact resolve eq647 eq18377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq18398 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18377
       grind)
    | exact superpose eq18377 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18377
  have eq18399 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18398
  have eq18401 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18394
  have eq18404 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18399
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18399
    | exact resolve eq18399 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18399
  have eq18405 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18404
  have eq18409 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18401
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18401
    | exact resolve eq18401 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18401
  have eq18422 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18405
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18405
    | exact resolve eq18405 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18405
  have eq18423 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18422
  have eq18427 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18409
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18409
    | exact resolve eq18409 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18409
  have eq18434 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq18427
    | exact resolve eq18427 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18427
  have eq18435 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18434
  have eq18440 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18435
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18435
    | exact resolve eq18435 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18435
  have eq18446 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18440
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18440
    | exact resolve eq18440 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18440
  have eq18451 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq18446
    | exact resolve eq18446 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18446
  have eq18452 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18451
  have eq18458 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18452
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18452
    | exact resolve eq18452 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18452
  have eq18465 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18458
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18458
    | exact resolve eq18458 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18458
  have eq18514 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18423
       grind)
    | exact superpose eq18423 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq18423
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18423
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18423
       grind)
    | exact resolve eq13 eq18423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18423
  have eq18517 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18514
  have eq18518 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18517
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18517
    | exact resolve eq18517 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18517
  have eq18519 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18518
  have eq18520 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18519
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18519
    | exact resolve eq18519 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18519
  have eq18530 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18465 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18465
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq18465
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18465
       grind)
    | exact resolve eq13 eq18465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18465
  have eq18533 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18530
  have eq18534 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq18533
    | exact resolve eq18533 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18533
  have eq18535 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18534
  have eq18536 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq18535
    | exact resolve eq18535 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18535
  have eq18802 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq18520
       grind)
    | exact superpose eq18520 eq71
    | exact resolve eq71 eq18520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18520
  have eq18830 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq18802
    | exact resolve eq18802 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18802
  have eq19152 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18830 eq18536
    | exact resolve eq18536 eq18830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18536 eq18830
  have eq19159 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq19152
  have eq19161 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19159
       have r₂ := eq27
       grind)
    | exact resolve eq19159 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19159
  have eq19172 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19161 eq65
    | (have r₁ := eq65
       have r₂ := eq19161
       grind)
    | exact resolve eq65 eq19161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq19175 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19161 eq27
    | exact resolve eq27 eq19161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19176 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq19161
  have eq19177 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq19172
  have eq23413 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19177
       have r₂ := eq19176
       grind)
    | exact resolve eq19177 eq19176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19177
  have eq23679 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23413 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq23413
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq23413
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq23413
       grind)
    | exact resolve eq14 eq23413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23413
  have eq23680 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq23679
  have eq23690 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23680 eq101
    | exact resolve eq101 eq23680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq23680
  have eq23713 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23690
  have eq23722 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq23713
       have r₂ := eq19175
       grind)
    | exact resolve eq23713 eq19175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19175 eq23713
  have eq41785 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23722 eq55
    | exact resolve eq55 eq23722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq23722
  have eq41831 : x = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq41785
    | exact resolve eq41785 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41785
  have eq41837 : y = (M.op y x) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq41831
       have r₂ := eq64
       grind)
    | exact resolve eq41831 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41831
  have eq41839 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq41837
       grind)
    | exact superpose eq41837 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq41837
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq41837
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq41837
       grind)
    | exact resolve eq13 eq41837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41840 : y ≠ y ∨ y = (k x y) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq41837
       grind)
    | exact superpose eq41837 eq14
    | (have j0 := eq14 x y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq41837
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq41837
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq41837
       grind)
    | exact resolve eq14 eq41837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41837
  have eq41841 : y = (k x y) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41840
  have eq41842 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41839
  have eq41843 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41842
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41842
    | exact resolve eq41842 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41842
  have eq41844 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41843
  have eq41845 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41844
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41844
    | exact resolve eq41844 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41844
  have eq41846 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq41841
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq41841
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq41841 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41841
  have eq41867 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq41846
  have eq41882 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq41867
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41867
    | exact resolve eq41867 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41867
  have eq41888 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq41882
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41882
    | exact resolve eq41882 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41882
  have eq41889 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq41888
  have eq42223 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq41889
       grind)
    | exact superpose eq41889 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq41889
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq41889
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq41889
       grind)
    | exact resolve eq13 eq41889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42224 : y ≠ y ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq41889
       grind)
    | exact superpose eq41889 eq14
    | (have j0 := eq14 x y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq41889
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq41889
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq41889
       grind)
    | exact resolve eq14 eq41889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41889
  have eq42225 : y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq42224
  have eq42226 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq42223
  have eq42227 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42226
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42226
    | exact resolve eq42226 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42226
  have eq42228 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq42227
  have eq42229 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq42228
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42228
    | exact resolve eq42228 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42228
  have eq42243 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq666 x y
       have i₂ := eq42225
       grind)
    | exact superpose eq42225 eq666
    | (have j0 := eq666 x y
       grind)
    | exact resolve eq666 eq42225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42225
  have eq42247 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq42243
  have eq42252 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42247
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq42247
    | exact resolve eq42247 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42247
  have eq42266 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42252
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq42252
    | exact resolve eq42252 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42252
  have eq42270 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq42266
       have r₂ := eq19176
       grind)
    | exact resolve eq42266 eq19176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19176 eq42266
  have eq42273 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42270
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq42270
    | exact resolve eq42270 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42270
  have eq42275 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42273
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq42273
    | exact resolve eq42273 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42273
  have eq42277 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42275
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq42275
    | exact resolve eq42275 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42275
  have eq42279 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42277
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq42277
    | exact resolve eq42277 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42277
  have eq42280 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq42279
    | exact resolve eq42279 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42279
  have eq42281 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq42280
  have eq42582 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq42229
       grind)
    | exact superpose eq42229 eq71
    | exact resolve eq71 eq42229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42229
  have eq42653 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq42582
    | exact resolve eq42582 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42582
  have eq42725 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42281 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq42281
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq42281
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq42281
       grind)
    | exact resolve eq13 eq42281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42281
  have eq42728 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq42725
  have eq42729 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq42728
    | exact resolve eq42728 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42728
  have eq42730 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq42729
  have eq42731 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq42730
    | exact resolve eq42730 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42730
  have eq43167 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42731 eq42653
    | exact resolve eq42653 eq42731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42653 eq42731
  have eq43174 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43167
  have eq43206 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq43174
       have r₂ := eq27
       grind)
    | exact resolve eq43174 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43174
  have eq43509 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43206 eq51
    | (have r₁ := eq51
       have r₂ := eq43206
       grind)
    | exact resolve eq51 eq43206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43206
  have eq43512 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq43509
  have eq43824 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43512 eq78
    | exact resolve eq78 eq43512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43512
  have eq43880 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq43824
    | exact resolve eq43824 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43824
  have eq43887 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq43880
       have r₂ := eq50
       grind)
    | exact resolve eq43880 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43880
  have eq43892 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq43887
       grind)
    | exact superpose eq43887 eq71
    | exact resolve eq71 eq43887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43909 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq666 y x
       have i₂ := eq43887
       grind)
    | exact superpose eq43887 eq666
    | (have j0 := eq666 y x
       grind)
    | exact resolve eq666 eq43887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq43911 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq43887
       grind)
    | exact superpose eq43887 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq43887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43912 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq43911
  have eq43913 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq43909
  have eq43925 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43912
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq43912
    | exact resolve eq43912 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43912
  have eq43927 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43913
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43913
    | exact resolve eq43913 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43913
  have eq43940 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43892
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43892
    | exact resolve eq43892 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43892
  have eq43944 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43927
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43927
    | exact resolve eq43927 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43927
  have eq43949 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43944
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43944
    | exact resolve eq43944 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43944
  have eq43954 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43949
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43949
    | exact resolve eq43949 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43949
  have eq43959 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq43954
    | exact resolve eq43954 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43954
  have eq43964 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43959
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43959
    | exact resolve eq43959 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43959
  have eq43969 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43964
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43964
    | exact resolve eq43964 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43964
  have eq48050 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq43969 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq43969
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq43969
       grind)
    | exact resolve eq13 eq43969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43969
  have eq48053 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq48050
  have eq48054 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq48053
    | exact resolve eq48053 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48053
  have eq48055 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq48054
  have eq48056 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq48055
    | exact resolve eq48055 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48055
  have eq48651 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq48056 eq43940
    | exact resolve eq43940 eq48056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48056
  have eq48662 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq48651
  have eq59452 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq43925
       grind)
    | exact superpose eq43925 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq43925
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq43925
       grind)
    | exact resolve eq13 eq43925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43925
  have eq59456 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq59452
  have eq59457 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq59456
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59456
    | exact resolve eq59456 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59456
  have eq59458 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq59457
  have eq59459 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq59458
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59458
    | exact resolve eq59458 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59458
  have eq59985 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43887
       have i₂ := eq59459
       grind)
    | exact superpose eq59459 eq43887
    | exact resolve eq43887 eq59459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59459
  have eq60033 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq59985
  have eq60132 : x ≠ x ∨ x = y ∨ x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq60033
       grind)
    | exact superpose eq60033 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq60033
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq60033
       grind)
    | exact resolve eq12 eq60033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60133 : x ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq60033
       grind)
    | exact superpose eq60033 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq60033
       grind)
    | exact resolve eq13 eq60033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60033
  have eq60135 : x = y ∨ x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq60132
  have eq60145 : x = (M.op x y) ∨ x ≠ y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60133
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60133
    | exact resolve eq60133 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60133
  have eq60146 : x = (M.op x y) ∨ x ≠ y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq60145
  have eq60147 : x = (M.op x y) ∨ x = y ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60135
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60135
    | exact resolve eq60135 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60135
  have eq60148 : y = (k y x) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq60147
  have eq60152 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x ≠ y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq60146
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60146
    | exact resolve eq60146 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60146
  have eq60199 : x = y ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43887
       have i₂ := eq60148
       grind)
    | exact superpose eq60148 eq43887
    | exact resolve eq43887 eq60148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60148
  have eq60251 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq60199
  have eq60356 : y ≠ y ∨ x = y ∨ y = (M.op y x) ∨ x = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq60251 eq64
    | (have r₁ := eq64
       have r₂ := eq60251
       grind)
    | exact resolve eq64 eq60251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq60468 : y ≠ y ∨ x = y ∨ y = (M.op y x) ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq60356
  have eq60469 : x = y ∨ y = (M.op y x) ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq60468
  have eq66129 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq60152
       have r₂ := eq60251
       grind)
    | exact resolve eq60152 eq60251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60152 eq60251
  have eq66167 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq43887
       have i₂ := eq66129
       grind)
    | exact superpose eq66129 eq43887
    | exact resolve eq43887 eq66129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66129
  have eq66216 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq66167
  have eq66307 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66216 eq20
    | exact resolve eq20 eq66216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66317 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq66216 eq118
    | exact resolve eq118 eq66216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq66366 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq66216 eq411
    | exact resolve eq411 eq66216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq66428 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq66216
  have eq66490 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq66366 X0
       have i₂ := eq410 X0
       grind)
    | exact superpose eq410 eq66366
    | exact resolve eq66366 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq66366
  have eq66538 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq66317 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq66317
    | exact resolve eq66317 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq66317
  have eq66547 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66307
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq66307
    | exact resolve eq66307 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66307
  have eq67219 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66547 eq26
    | exact resolve eq26 eq66547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67286 : (σ x) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66547 eq6865
    | exact resolve eq6865 eq66547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6865
  have eq67287 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66547 eq7660
    | exact resolve eq7660 eq66547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7660
  have eq67408 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq67287
       have r₂ := eq27
       grind)
    | exact resolve eq67287 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67287
  have eq67409 : (σ x) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq67286
       have r₂ := eq27
       grind)
    | exact resolve eq67286 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67286
  have eq67796 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq67219 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq67219
       grind)
    | exact resolve eq14 eq67219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67219
  have eq71235 : ∀ X0 : G, (k X0 (σ y)) = (σ (τ (k X0 (σ (M.op x y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq66490 eq15
    | exact resolve eq15 eq66490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66490
  have eq71572 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq71235 X0
       have i₂ := eq15 (k X0 sF1)
       grind)
    | exact superpose eq15 eq71235
    | exact resolve eq71235 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71235
  have eq189114 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3000 y
       have i₂ := eq41845
       grind)
    | exact superpose eq41845 eq3000
    | (have j0 := eq3000 y
       grind)
    | exact resolve eq3000 eq41845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41845
  have eq189116 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3000 y
       have i₂ := eq43887
       grind)
    | exact superpose eq43887 eq3000
    | (have j0 := eq3000 y
       grind)
    | exact resolve eq3000 eq43887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3000 eq43887
  have eq189223 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq189116
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq189116
    | exact resolve eq189116 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189116
  have eq189224 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq189114
    | exact resolve eq189114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189114
  have eq189282 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq189223
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq189223
    | exact resolve eq189223 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189223
  have eq189283 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq189224
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq189224
    | exact resolve eq189224 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189224
  have eq189341 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq189282
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq189282
    | exact resolve eq189282 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189282
  have eq189342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq189283
       have r₂ := eq66547
       grind)
    | exact resolve eq189283 eq66547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189283
  have eq189400 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq189341
    | exact resolve eq189341 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189341
  have eq189401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq189342
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq189342
    | exact resolve eq189342 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189342
  have eq189433 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq189400
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq189400
    | exact resolve eq189400 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189400
  have eq189434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq189401
    | exact resolve eq189401 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189401
  have eq189464 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq189433
       have r₂ := eq48662
       grind)
    | exact resolve eq189433 eq48662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189433
  have eq189465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq189434
    | exact resolve eq189434 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189434
  have eq189486 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq189464
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq189464
    | exact resolve eq189464 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189464
  have eq189487 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq189465
       have r₂ := eq27
       grind)
    | exact resolve eq189465 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189465
  have eq189492 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq189486
    | exact resolve eq189486 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189486
  have eq189493 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq189492
  have eq189494 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq189487
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq189487
    | exact resolve eq189487 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189487
  have eq189497 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq189493
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq189493
    | exact resolve eq189493 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189493
  have eq189498 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq189494
    | exact resolve eq189494 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189494
  have eq189499 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq189498
  have eq189501 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq189499
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq189499
    | exact resolve eq189499 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189499
  have eq189520 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq189497 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq189497
       grind)
    | exact resolve eq13 eq189497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189497
  have eq189539 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq189520
       have r₂ := eq48662
       grind)
    | exact resolve eq189520 eq48662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48662 eq189520
  have eq189540 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq189539
    | exact resolve eq189539 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189539
  have eq189541 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq189540
  have eq189542 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq189541
    | exact resolve eq189541 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189541
  have eq189710 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq189542 eq43940
    | exact resolve eq43940 eq189542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43940 eq189542
  have eq189791 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq189710
  have eq190277 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq189791 eq27
    | exact resolve eq27 eq189791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189791
  have eq418267 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66547 eq189501
    | exact resolve eq189501 eq66547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189501
  have eq418304 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq418267
  have eq502902 : y = (M.op y x) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq60469
       have r₂ := eq66428
       grind)
    | exact resolve eq60469 eq66428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60469
  have eq502905 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq502902
       grind)
    | exact superpose eq502902 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq502902
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq502902
       grind)
    | exact resolve eq13 eq502902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502906 : y ≠ y ∨ y = (k x y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq502902
       grind)
    | exact superpose eq502902 eq14
    | (have j0 := eq14 x y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq502902
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq502902
       grind)
    | exact resolve eq14 eq502902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502902
  have eq502907 : y = (k x y) ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq502906
  have eq502908 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq502905
  have eq502911 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq502908
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq502908
    | exact resolve eq502908 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502908
  have eq502912 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (k x y) := by grind
  clear eq502911
  have eq502913 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq502912
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq502912
    | exact resolve eq502912 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502912
  have eq503308 : (σ y) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq502907
       grind)
    | exact superpose eq502907 eq44
    | exact resolve eq44 eq502907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502907
  have eq503443 : (σ y) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq503308
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq503308
    | exact resolve eq503308 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503308
  have eq503596 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq502913
       grind)
    | exact superpose eq502913 eq71
    | exact resolve eq71 eq502913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq502913
  have eq503822 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq503596
    | exact resolve eq503596 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503596
  have eq503992 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66547 eq503443
    | exact resolve eq503443 eq66547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66547 eq503443
  have eq504119 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq503992
  have eq504692 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq503822 eq66538
    | exact resolve eq66538 eq503822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66538 eq503822
  have eq504739 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq504692
  have eq631601 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq504119 eq67408
    | (have r₁ := eq67408
       have r₂ := eq504119
       grind)
    | exact resolve eq67408 eq504119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67408 eq504119
  have eq631606 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq631601
  have eq631607 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq631606
  have eq1978972 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq631607 eq418304
    | exact resolve eq418304 eq631607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418304 eq631607
  have eq1978977 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1978972
  have eq1978988 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1978977
       grind)
    | exact superpose eq1978977 eq44
    | exact resolve eq44 eq1978977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1978977
  have eq1979270 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1978988
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1978988
    | exact resolve eq1978988 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1978988
  have eq1979533 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1979270 eq71572
    | exact resolve eq71572 eq1979270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71572 eq1979270
  have eq1979628 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1979533
  have eq1979843 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1979628 eq67409
    | (have r₁ := eq67409
       have r₂ := eq1979628
       grind)
    | exact resolve eq67409 eq1979628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67409
  have eq1979906 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1979843
  have eq1979907 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1979906
  have eq1980467 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1979907 eq14
    | (have j0 := eq14 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq14 (σ x) (σ (M.op x y))
       have r₂ := eq1979907
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq1979907
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq1979907
       grind)
    | exact resolve eq14 eq1979907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979907
  have eq1980468 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1980467
  have eq1980540 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1980468 eq1979628
    | exact resolve eq1979628 eq1980468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979628 eq1980468
  have eq1980587 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1980540
  have eq1980662 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1980587 eq51
    | (have r₁ := eq51
       have r₂ := eq1980587
       grind)
    | exact resolve eq51 eq1980587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1980664 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1980587 eq67796
    | (have r₁ := eq67796
       have r₂ := eq1980587
       grind)
    | exact resolve eq67796 eq1980587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67796 eq1980587
  have eq1980665 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1980664
  have eq1980666 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1980665
  have eq1980668 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1980662
  have eq1980725 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1980666 eq504739
    | exact resolve eq504739 eq1980666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504739 eq1980666
  have eq1980784 : x = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1980725
  have eq1980865 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1980668 eq78
    | exact resolve eq78 eq1980668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1980668
  have eq1981214 : x = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq1980865
    | exact resolve eq1980865 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980865
  have eq1981232 : x = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1981214
       have r₂ := eq50
       grind)
    | exact resolve eq1981214 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981214
  have eq2062801 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq6064 y x
       have i₂ := eq1981232
       grind)
    | exact superpose eq1981232 eq6064
    | (have j0 := eq6064 y x
       grind)
    | (have r₁ := eq6064 y x
       have r₂ := eq1981232
       grind)
    | exact resolve eq6064 eq1981232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6064 eq1981232
  have eq2063301 : x = (M.op x y) ∨ x = y ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2062801
  have eq2063360 : x = (M.op x y) ∨ x = y ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2063301
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2063301
    | exact resolve eq2063301 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2063301
  have eq2063397 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq2063360
       have r₂ := eq66428
       grind)
    | exact resolve eq2063360 eq66428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2063360
  have eq2063403 : y ≠ y ∨ y = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq2063397
       grind)
    | exact superpose eq2063397 eq14
    | (have j0 := eq14 x y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq2063397
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq2063397
       grind)
    | exact resolve eq14 eq2063397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2063397
  have eq2063404 : y = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2063403
  have eq2063511 : x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1980784
       have i₂ := eq2063404
       grind)
    | exact superpose eq2063404 eq1980784
    | exact resolve eq1980784 eq2063404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980784 eq2063404
  have eq2063581 : x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2063511
  have eq2063636 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2063581
       have r₂ := eq66428
       grind)
    | exact resolve eq2063581 eq66428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66428 eq2063581
  have eq2063834 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2063636 eq28
    | exact resolve eq28 eq2063636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2063636
  have eq2064907 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2063834
    | exact resolve eq2063834 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2063834
  have eq2064908 : x = (M.op x y) := by grind
  clear eq2064907
  have eq2064911 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2064908 eq20
    | exact resolve eq20 eq2064908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2064913 : x ≠ x ∨ x = (k y x) := by
    first
    | exact superpose eq2064908 eq50
    | (have r₁ := eq50
       have r₂ := eq2064908
       grind)
    | exact resolve eq50 eq2064908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq2065541 : x = (k y x) := by grind
  clear eq2064913
  have eq2066090 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2064911
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2064911
    | exact resolve eq2064911 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2064911
  have eq2066093 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2066090 eq26
    | exact resolve eq26 eq2066090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2066594 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2066090 eq190277
    | (have r₁ := eq190277
       have r₂ := eq2066090
       grind)
    | exact resolve eq190277 eq2066090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190277
  have eq2066698 : y = (M.op x y) := by grind
  clear eq2066594
  have eq2066730 : x = y := by
    first
    | exact superpose eq2064908 eq2066698
    | exact resolve eq2066698 eq2064908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2064908 eq2066698
  have eq2067103 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2066730
       grind)
    | exact superpose eq2066730 eq24
    | exact resolve eq24 eq2066730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2068900 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2067103
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2067103
    | exact resolve eq2067103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2067103
  have eq2069452 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2066090 eq2068900
    | exact resolve eq2068900 eq2066090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068900
  have eq2071709 : x = (k x x) := by
    first
    | (have i₁ := eq2065541
       have i₂ := eq2066730
       grind)
    | exact superpose eq2066730 eq2065541
    | exact resolve eq2065541 eq2066730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065541 eq2066730
  have eq2071817 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq664 x x
       have i₂ := eq2071709
       grind)
    | exact superpose eq2071709 eq664
    | (have j0 := eq664 x x
       grind)
    | exact resolve eq664 eq2071709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq2071709
  have eq2071829 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2071817
  have eq2071830 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2071829
  have eq2071858 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2071830
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2071830
    | exact resolve eq2071830 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2071830
  have eq2071961 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2066090 eq2071858
    | exact resolve eq2071858 eq2066090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2066090 eq2071858
  have eq2072292 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2069452 eq2066093
    | exact resolve eq2066093 eq2069452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2066093 eq2069452
  have eq2072934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2071961 eq2072292
    | exact resolve eq2072292 eq2071961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071961 eq2072292
  have eq2072935 : False := by grind
  exact eq2072935

/-- `x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = Y then X else if m(X,Y) = X then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyx_y_pxy_y_pxy_x_pyx_x_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq50 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
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
  have eq56 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) := by
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
  have eq57 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq68 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  clear eq44
  have eq74 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq68
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq69
    | exact resolve eq69 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq76
    | exact resolve eq76 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq80 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80
    | exact resolve eq80 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq88 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq90 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq113 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq146 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
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
  clear eq39
  have eq186 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
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
  have eq675 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq100 (σ X0) (σ X1)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq100
    | (have j0 := eq100 (σ X0) (σ X1)
       have j1 := eq64 X0 X1
       grind)
    | (have r₁ := eq100 (σ X1) (σ X1)
       have r₂ := eq64 X1 X1
       grind)
    | (have r₁ := eq100 (σ X0) (σ X1)
       have r₂ := eq64 X0 X1
       grind)
    | (have r₁ := eq100 (σ X1) (σ X0)
       have r₂ := eq64 X0 X1
       grind)
    | exact resolve eq100 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq64 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq64 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq64 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq64 X1 X1
       grind)
    | exact resolve eq13 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq682 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq676 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq684 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq682 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq682 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq682 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq682 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | exact resolve eq682 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq685 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq675 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq675 X1 X1
       have r₂ := eq14 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq675 X0 X1
       have r₂ := eq14 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq675 X0 X1
       have r₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq675 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq694 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq684 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq684
    | (have j0 := eq684 X0 X1
       grind)
    | exact resolve eq684 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq695 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq685 X0 X1
       have j1 := eq100 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq685 X1 X1
       have r₂ := eq100 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq685 X0 X1
       have r₂ := eq100 (σ X0) (σ X1)
       grind)
    | exact resolve eq685 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq702 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq695
    | (have j0 := eq695 X0 X1
       grind)
    | exact resolve eq695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq2966 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  clear eq146
  have eq2975 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2966
  have eq2981 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2975
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq2975
    | exact resolve eq2975 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2975
  have eq2999 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | (have r₁ := eq2981
       have r₂ := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq2981 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2981
  have eq3006 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq2999 eq49
    | exact resolve eq49 eq2999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq3131 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq186 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq3729 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (k (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ y) (σ X0)
       have j1 := eq91 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ X0)
       have r₂ := eq91 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq91 y
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq3733 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (k (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3729 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3729
  have eq3736 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (k (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3733 X0
       have j1 := eq13 (σ y) (σ X0)
       grind)
    | (have r₁ := eq3733 y
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq3733 X0
       have r₂ := eq13 (σ y) (σ X0)
       grind)
    | exact resolve eq3733 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3733
  have eq3774 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq3736
    | (have j0 := eq3736 X0
       grind)
    | exact resolve eq3736 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq3736
  have eq10433 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2999 eq74
    | exact resolve eq74 eq2999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq2999
  have eq13947 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq10433
       grind)
    | exact superpose eq10433 eq16
    | exact resolve eq16 eq10433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10433
  have eq13994 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3006 eq13947
    | exact resolve eq13947 eq3006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13947
  have eq13997 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq14 x x
       grind)
    | (have r₁ := eq13994
       have r₂ := eq14 x x
       grind)
    | exact resolve eq13994 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13994
  have eq22252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq81 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22253 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq22252
    | exact resolve eq22252 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22252
  have eq22264 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq22253
       have r₂ := eq27
       grind)
    | exact resolve eq22253 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22253
  have eq22268 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq22264
    | exact resolve eq22264 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22264
  have eq22270 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq22268
    | exact resolve eq22268 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22268
  have eq22274 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq22270 eq14
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq22270
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq22270
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq22270
       grind)
    | exact resolve eq14 eq22270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22270
  have eq22275 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq22274
  have eq22285 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq22275 eq55
    | exact resolve eq55 eq22275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22275
  have eq22309 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq22285
    | exact resolve eq22285 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22285
  have eq23854 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq22309
       grind)
    | exact superpose eq22309 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq22309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22309
  have eq23855 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23854
  have eq23859 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23855
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23855
    | exact resolve eq23855 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23855
  have eq23860 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23859
  have eq23875 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23860
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23860
    | exact resolve eq23860 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23860
  have eq23876 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23875
  have eq23904 : y ≠ y ∨ x = y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq100 y x
       have i₂ := eq23876
       grind)
    | exact superpose eq23876 eq100
    | (have j0 := eq100 x y
       grind)
    | (have r₁ := eq100 y x
       have r₂ := eq23876
       grind)
    | (have r₁ := eq100 x y
       have r₂ := eq23876
       grind)
    | (have r₁ := eq100 (σ x) (σ y)
       have r₂ := eq23876
       grind)
    | exact resolve eq100 eq23876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23906 : y ≠ y ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq23876
       grind)
    | exact superpose eq23876 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq23876
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq23876
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq23876
       grind)
    | exact resolve eq14 eq23876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23876
  have eq23907 : y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23906
  have eq23908 : x = y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23904
  have eq23911 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23908
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23908
    | exact resolve eq23908 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23908
  have eq23912 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq23911
       have r₂ := eq50
       grind)
    | exact resolve eq23911 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23911
  have eq24225 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq678 x y
       have i₂ := eq23907
       grind)
    | exact superpose eq23907 eq678
    | (have j0 := eq678 x y
       grind)
    | exact resolve eq678 eq23907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq23907
  have eq24230 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24225
  have eq24233 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24230
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24230
    | exact resolve eq24230 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24230
  have eq24245 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24233
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24233
    | exact resolve eq24233 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24233
  have eq24250 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq24245
    | exact resolve eq24245 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24245
  have eq24251 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24250
  have eq24254 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24251
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24251
    | exact resolve eq24251 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24251
  have eq24257 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24254
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24254
    | exact resolve eq24254 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24254
  have eq24261 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq24257
    | exact resolve eq24257 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24257
  have eq24262 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq24261
  have eq24266 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24262
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24262
    | exact resolve eq24262 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24262
  have eq24268 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24266
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24266
    | exact resolve eq24266 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24266
  have eq24275 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq88
       have i₂ := eq23912
       grind)
    | exact superpose eq23912 eq88
    | exact resolve eq88 eq23912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23912
  have eq24305 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq24275
    | exact resolve eq24275 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24275
  have eq24693 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24268 eq100
    | (have j0 := eq100 (σ x) (σ y)
       grind)
    | (have r₁ := eq100 (σ y) (σ x)
       have r₂ := eq24268
       grind)
    | (have r₁ := eq100 (σ x) (σ y)
       have r₂ := eq24268
       grind)
    | (have r₁ := eq100 x y
       have r₂ := eq24268
       grind)
    | exact resolve eq100 eq24268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24268
  have eq24697 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq24693
  have eq24700 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq24697
    | exact resolve eq24697 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24697
  have eq24701 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq24700
       have r₂ := eq51
       grind)
    | exact resolve eq24700 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24700
  have eq25054 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24701 eq24305
    | exact resolve eq24305 eq24701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24305 eq24701
  have eq25060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq25054
  have eq25065 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq25060
       have r₂ := eq27
       grind)
    | exact resolve eq25060 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25060
  have eq25430 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25065 eq57
    | (have r₁ := eq57
       have r₂ := eq25065
       grind)
    | exact resolve eq57 eq25065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq25432 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25065 eq27
    | exact resolve eq27 eq25065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25065
  have eq25434 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq25430
  have eq82330 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25434 eq14
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq25434
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq25434
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq25434
       grind)
    | exact resolve eq14 eq25434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25434
  have eq82331 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq82330
  have eq150184 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82331 eq81
    | exact resolve eq81 eq82331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq82331
  have eq150237 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq150184
  have eq150247 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq150237
       have r₂ := eq25432
       grind)
    | exact resolve eq150237 eq25432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25432 eq150237
  have eq211209 : (τ (σ x)) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq150247 eq55
    | exact resolve eq55 eq150247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq150247
  have eq211423 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28 eq211209
    | exact resolve eq211209 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211209
  have eq211432 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq211423
       have r₂ := eq56
       grind)
    | exact resolve eq211423 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq211423
  have eq211435 : y ≠ y ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq100 y x
       have i₂ := eq211432
       grind)
    | exact superpose eq211432 eq100
    | (have j0 := eq100 y x
       grind)
    | (have r₁ := eq100 y x
       have r₂ := eq211432
       grind)
    | (have r₁ := eq100 x y
       have r₂ := eq211432
       grind)
    | (have r₁ := eq100 (σ x) (σ y)
       have r₂ := eq211432
       grind)
    | exact resolve eq100 eq211432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211437 : y ≠ y ∨ y = (k x y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq211432
       grind)
    | exact superpose eq211432 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq211432
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq211432
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq211432
       grind)
    | exact resolve eq14 eq211432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211432
  have eq211438 : y = (k x y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq211437
  have eq211439 : y ≠ y ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq211435
  have eq211440 : x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq211439
  have eq211441 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq211440
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq211440
    | exact resolve eq211440 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211440
  have eq211442 : (M.op x y) = (k y x) ∨ x = y ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq211441
       have r₂ := eq50
       grind)
    | exact resolve eq211441 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211441
  have eq211449 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq211442
       grind)
    | exact superpose eq211442 eq88
    | exact resolve eq88 eq211442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211442
  have eq211591 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq211449
    | exact resolve eq211449 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211449
  have eq211885 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq211438
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq211438
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq211438 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211922 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq694 x y
       have i₂ := eq211438
       grind)
    | exact superpose eq211438 eq694
    | (have j0 := eq694 x y
       grind)
    | exact resolve eq694 eq211438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211438
  have eq211926 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq211922
  have eq211949 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq211885
  have eq211951 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq211926
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq211926
    | exact resolve eq211926 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211926
  have eq211967 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq211949
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq211949
    | exact resolve eq211949 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211949
  have eq211968 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq211951
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq211951
    | exact resolve eq211951 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211951
  have eq211969 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq211968
  have eq211974 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq211967
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq211967
    | exact resolve eq211967 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211967
  have eq211975 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq211974
  have eq211976 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq211969
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq211969
    | exact resolve eq211969 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211969
  have eq211978 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq211976
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq211976
    | exact resolve eq211976 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211976
  have eq211980 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq211978
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq211978
    | exact resolve eq211978 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211978
  have eq211982 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq211980
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq211980
    | exact resolve eq211980 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211980
  have eq211985 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq211982
    | exact resolve eq211982 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211982
  have eq211986 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq211985
  have eq211989 : y ≠ y ∨ x = y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100 y x
       have i₂ := eq211975
       grind)
    | exact superpose eq211975 eq100
    | (have j0 := eq100 x y
       grind)
    | (have r₁ := eq100 y x
       have r₂ := eq211975
       grind)
    | (have r₁ := eq100 (σ x) (σ y)
       have r₂ := eq211975
       grind)
    | (have r₁ := eq100 x y
       have r₂ := eq211975
       grind)
    | exact resolve eq100 eq211975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211991 : y ≠ y ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq211975
       grind)
    | exact superpose eq211975 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq211975
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq211975
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq211975
       grind)
    | exact resolve eq14 eq211975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211975
  have eq211992 : y = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq211991
  have eq211993 : y ≠ y ∨ x = y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq211989
  have eq211994 : x = y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq211993
  have eq211995 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq211994
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq211994
    | exact resolve eq211994 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211994
  have eq211996 : (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq211995
       have r₂ := eq50
       grind)
    | exact resolve eq211995 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211995
  have eq212003 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq211996
       grind)
    | exact superpose eq211996 eq88
    | exact resolve eq88 eq211996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211996
  have eq212145 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq212003
    | exact resolve eq212003 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212003
  have eq212475 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq694 x y
       have i₂ := eq211992
       grind)
    | exact superpose eq211992 eq694
    | (have j0 := eq694 x y
       grind)
    | exact resolve eq694 eq211992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq211992
  have eq212478 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq212475
  have eq212502 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq212478
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq212478
    | exact resolve eq212478 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212478
  have eq212518 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq212502
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq212502
    | exact resolve eq212502 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212502
  have eq212519 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq212518
  have eq212524 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq212519
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq212519
    | exact resolve eq212519 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212519
  have eq212526 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq212524
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq212524
    | exact resolve eq212524 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212524
  have eq212527 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq212526
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq212526
    | exact resolve eq212526 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212526
  have eq212528 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq212527
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq212527
    | exact resolve eq212527 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212527
  have eq212529 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq212528
    | exact resolve eq212528 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212528
  have eq212530 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq212529
  have eq212638 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq212530 eq100
    | (have j0 := eq100 x y
       grind)
    | (have r₁ := eq100 (σ y) (σ x)
       have r₂ := eq212530
       grind)
    | (have r₁ := eq100 (σ x) (σ y)
       have r₂ := eq212530
       grind)
    | (have r₁ := eq100 x y
       have r₂ := eq212530
       grind)
    | exact resolve eq100 eq212530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212530
  have eq212642 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq212638
  have eq212643 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq212642
  have eq212645 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq212643
    | exact resolve eq212643 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212643
  have eq212646 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq212645
       have r₂ := eq51
       grind)
    | exact resolve eq212645 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212645
  have eq212764 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq212646 eq212145
    | exact resolve eq212145 eq212646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212145 eq212646
  have eq212774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq212764
  have eq212884 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq212774
       have r₂ := eq27
       grind)
    | exact resolve eq212774 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212774
  have eq212896 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq212884 eq51
    | (have r₁ := eq51
       have r₂ := eq212884
       grind)
    | exact resolve eq51 eq212884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212884
  have eq212963 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq212896
  have eq212993 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq212963 eq98
    | exact resolve eq98 eq212963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212963
  have eq213356 : x = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq212993
    | exact resolve eq212993 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212993
  have eq213503 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq213356
       grind)
    | exact superpose eq213356 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq213356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213504 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq213503
  have eq213626 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq213504
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq213504
    | exact resolve eq213504 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213504
  have eq213627 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq213626
  have eq267156 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq211986 eq100
    | (have j0 := eq100 (σ y) (σ x)
       grind)
    | (have r₁ := eq100 (σ y) (σ x)
       have r₂ := eq211986
       grind)
    | (have r₁ := eq100 (σ x) (σ y)
       have r₂ := eq211986
       grind)
    | (have r₁ := eq100 x y
       have r₂ := eq211986
       grind)
    | exact resolve eq100 eq211986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211986
  have eq267160 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq267156
  have eq267161 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq267160
  have eq267164 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq26 eq267161
    | exact resolve eq267161 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267161
  have eq267166 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have r₁ := eq267164
       have r₂ := eq51
       grind)
    | exact resolve eq267164 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267164
  have eq267648 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq267166 eq211591
    | exact resolve eq211591 eq267166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211591 eq267166
  have eq267687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq267648
  have eq267797 : x = (k x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq267687
       have r₂ := eq27
       grind)
    | exact resolve eq267687 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267687
  have eq267901 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3131 x
       have i₂ := eq267797
       grind)
    | exact superpose eq267797 eq3131
    | (have j0 := eq3131 x
       grind)
    | exact resolve eq3131 eq267797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3131
  have eq267905 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq702 x y
       have i₂ := eq267797
       grind)
    | exact superpose eq267797 eq702
    | (have j0 := eq702 y x
       grind)
    | exact resolve eq702 eq267797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq267797
  have eq267911 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq267905
  have eq267912 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq267901
  have eq268002 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq267911
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq267911
    | exact resolve eq267911 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267911
  have eq268006 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq267912
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq267912
    | exact resolve eq267912 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267912
  have eq268025 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq268002
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq268002
    | exact resolve eq268002 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268002
  have eq268028 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq268006
    | exact resolve eq268006 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268006
  have eq268033 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq268025
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq268025
    | exact resolve eq268025 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268025
  have eq268036 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq268028
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq268028
    | exact resolve eq268028 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268028
  have eq268038 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq268033
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq268033
    | exact resolve eq268033 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268033
  have eq268039 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq268038
  have eq268042 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq268036
    | exact resolve eq268036 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268036
  have eq268043 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq268042
  have eq268045 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq268039
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq268039
    | exact resolve eq268039 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268039
  have eq268046 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq268043
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq268043
    | exact resolve eq268043 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268043
  have eq268049 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq268045
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq268045
    | exact resolve eq268045 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268045
  have eq268051 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq268049
    | exact resolve eq268049 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268049
  have eq269981 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq268051 eq268046
    | exact resolve eq268046 eq268051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268046 eq268051
  have eq269985 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq269981
  have eq270367 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq269985 eq27
    | exact resolve eq27 eq269985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269985
  have eq285179 : y ≠ y ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq100 y x
       have i₂ := eq213627
       grind)
    | exact superpose eq213627 eq100
    | (have j0 := eq100 y x
       grind)
    | (have r₁ := eq100 y x
       have r₂ := eq213627
       grind)
    | (have r₁ := eq100 x y
       have r₂ := eq213627
       grind)
    | exact resolve eq100 eq213627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213627
  have eq285184 : y ≠ y ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq285179
  have eq285185 : x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq285184
  have eq285186 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq285185
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq285185
    | exact resolve eq285185 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285185
  have eq285187 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq285186
       have r₂ := eq50
       grind)
    | exact resolve eq285186 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285186
  have eq286153 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq213356
       have i₂ := eq285187
       grind)
    | exact superpose eq285187 eq213356
    | exact resolve eq213356 eq285187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285187
  have eq286192 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq286153
  have eq286407 : x ≠ x ∨ x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq286192
       grind)
    | exact superpose eq286192 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq286192
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq286192
       grind)
    | exact resolve eq13 eq286192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286192
  have eq286409 : x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq286407
  have eq286421 : x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq286409
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq286409
    | exact resolve eq286409 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286409
  have eq286422 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq286421
  have eq287087 : x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq213356
       have i₂ := eq286422
       grind)
    | exact superpose eq286422 eq213356
    | exact resolve eq213356 eq286422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213356 eq286422
  have eq287128 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq287087
  have eq287856 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq287128 eq29
    | exact resolve eq29 eq287128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287128
  have eq288568 : x = y ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq287856
    | exact resolve eq287856 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287856
  have eq288569 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq288568
  have eq288628 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq288569 eq20
    | exact resolve eq20 eq288569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288569
  have eq288975 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq288628
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq288628
    | exact resolve eq288628 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288628
  have eq289461 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq288975 eq270367
    | (have r₁ := eq270367
       have r₂ := eq288975
       grind)
    | exact resolve eq270367 eq288975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270367 eq288975
  have eq289464 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq289461
  have eq289465 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq289464
  have eq290939 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq289465 eq51
    | (have r₁ := eq51
       have r₂ := eq289465
       grind)
    | exact resolve eq51 eq289465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289465
  have eq291051 : (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq290939
  have eq297414 : (τ (σ x)) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq291051 eq98
    | exact resolve eq98 eq291051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291051
  have eq297836 : x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq297414
    | exact resolve eq297414 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297414
  have eq299543 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq297836
       grind)
    | exact superpose eq297836 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq297836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299544 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq299543
  have eq299699 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq299544
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq299544
    | exact resolve eq299544 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299544
  have eq299700 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq299699
  have eq2562669 : y ≠ y ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq100 y x
       have i₂ := eq299700
       grind)
    | exact superpose eq299700 eq100
    | (have j0 := eq100 y x
       grind)
    | (have r₁ := eq100 y x
       have r₂ := eq299700
       grind)
    | (have r₁ := eq100 x y
       have r₂ := eq299700
       grind)
    | exact resolve eq100 eq299700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299700
  have eq2562671 : y ≠ y ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2562669
  have eq2562672 : x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2562671
  have eq2562675 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2562672
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2562672
    | exact resolve eq2562672 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562672
  have eq2562676 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq2562675
       have r₂ := eq50
       grind)
    | exact resolve eq2562675 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562675
  have eq2562845 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq297836
       have i₂ := eq2562676
       grind)
    | exact superpose eq2562676 eq297836
    | exact resolve eq297836 eq2562676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562676
  have eq2563048 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2562845
  have eq2563470 : x ≠ x ∨ x = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2563048
       grind)
    | exact superpose eq2563048 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2563048
       grind)
    | exact resolve eq13 eq2563048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2563048
  have eq2563472 : x = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2563470
  have eq2563487 : x = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2563472
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2563472
    | exact resolve eq2563472 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2563472
  have eq2563488 : y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq2563487
  have eq2563732 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq297836
       have i₂ := eq2563488
       grind)
    | exact superpose eq2563488 eq297836
    | exact resolve eq297836 eq2563488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297836 eq2563488
  have eq2563957 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2563732
  have eq2564426 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2563957 eq28
    | exact resolve eq28 eq2563957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2563957
  have eq2566467 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2564426
    | exact resolve eq2564426 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2564426
  have eq2566468 : x = (M.op x y) ∨ x = y := by grind
  clear eq2566467
  have eq2566604 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2566468 eq20
    | exact resolve eq20 eq2566468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2566606 : x ≠ x ∨ x = (k y x) ∨ x = y := by
    first
    | exact superpose eq2566468 eq50
    | (have r₁ := eq50
       have r₂ := eq2566468
       grind)
    | exact resolve eq50 eq2566468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2566468
  have eq2567292 : x = (k y x) ∨ x = y := by grind
  clear eq2566606
  have eq2567855 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2566604
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2566604
    | exact resolve eq2566604 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2566604
  have eq2568051 : (k y x) = (τ (k (σ y) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq2567855 eq98
    | exact resolve eq98 eq2567855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq2569994 : (k y x) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq113 eq2568051
    | exact resolve eq2568051 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2568051
  have eq2570166 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq2567292
       grind)
    | exact superpose eq2567292 eq88
    | exact resolve eq88 eq2567292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2570454 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq3774 x
       have i₂ := eq2567292
       grind)
    | exact superpose eq2567292 eq3774
    | (have j0 := eq3774 x
       grind)
    | exact resolve eq3774 eq2567292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3774 eq2567292
  have eq2570490 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq2570454
  have eq2570703 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq2570490
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2570490
    | exact resolve eq2570490 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2570490
  have eq2570799 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq2570166
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2570166
    | exact resolve eq2570166 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2570166
  have eq2570812 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq2570703
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2570703
    | exact resolve eq2570703 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2570703
  have eq2570850 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq2570812
    | exact resolve eq2570812 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2570812
  have eq2570867 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2570850
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2570850
    | exact resolve eq2570850 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2570850
  have eq2570921 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2567855 eq2570799
    | exact resolve eq2570799 eq2567855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2567855 eq2570799
  have eq2571652 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq2570921
  have eq2571736 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2571652 eq113
    | exact resolve eq113 eq2571652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq2571652
  have eq2572148 : (M.op x y) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30 eq2571736
    | exact resolve eq2571736 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2571736
  have eq2579642 : (M.op x y) = (k y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2569994 eq2572148
    | exact resolve eq2572148 eq2569994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2569994 eq2572148
  have eq2579770 : (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq2579642
  have eq2580083 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq2579770
       grind)
    | exact superpose eq2579770 eq88
    | exact resolve eq88 eq2579770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq2579770
  have eq2580619 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq2580083
    | exact resolve eq2580083 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580083
  have eq2819376 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2570867 eq100
    | (have j0 := eq100 (σ y) (σ x)
       grind)
    | (have r₁ := eq100 (σ y) (σ x)
       have r₂ := eq2570867
       grind)
    | (have r₁ := eq100 (σ x) (σ y)
       have r₂ := eq2570867
       grind)
    | exact resolve eq100 eq2570867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq2570867
  have eq2819377 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq2819376
  have eq2819378 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq2819377
  have eq2819415 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq2819378
    | exact resolve eq2819378 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2819378
  have eq2819417 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2819415
       have r₂ := eq51
       grind)
    | exact resolve eq2819415 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2819415
  have eq2819731 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2819417 eq2580619
    | exact resolve eq2580619 eq2819417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580619 eq2819417
  have eq2819894 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2819731
  have eq2820163 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2819894
       have r₂ := eq27
       grind)
    | exact resolve eq2819894 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2819894
  have eq2820186 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2820163 eq29
    | exact resolve eq29 eq2820163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2820163
  have eq2823372 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq2820186
    | exact resolve eq2820186 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2820186
  have eq2823373 : x = y := by grind
  clear eq2823372
  have eq2823508 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2823373
       grind)
    | exact superpose eq2823373 eq18
    | exact resolve eq18 eq2823373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2823509 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2823373
       grind)
    | exact superpose eq2823373 eq24
    | exact resolve eq24 eq2823373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2823373
  have eq2825210 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2823509
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2823509
    | exact resolve eq2823509 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2823509
  have eq2825389 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2825210 eq26
    | exact resolve eq26 eq2825210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2825210
  have eq2828252 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2825389 eq3006
    | exact resolve eq3006 eq2825389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3006 eq2825389
  have eq2828364 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2828252
       have i₂ := eq13997
       grind)
    | exact superpose eq13997 eq2828252
    | exact resolve eq2828252 eq13997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13997 eq2828252
  have eq2828392 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2828364
       have i₂ := eq2823508
       grind)
    | exact superpose eq2823508 eq2828364
    | exact resolve eq2828364 eq2823508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2823508 eq2828364
  have eq2828490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2828392 eq15
    | exact resolve eq15 eq2828392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828392
  have eq2829305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2828490
    | exact resolve eq2828490 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2828490
  have eq2829535 : False := by grind
  exact eq2829535

/-- `x □ y = if m(Y,X) = Y then Y else if m(X,Y) = Y then X else if m(X,Y) = X then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyx_y_pxy_y_pxy_x_y_x_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
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
  have eq50 : x ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
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
  have eq56 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) := by
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
  have eq57 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq68 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  clear eq43
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq74 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq68
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq69
    | exact resolve eq69 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq76
    | exact resolve eq76 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq80 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80
    | exact resolve eq80 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq88 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq91 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq394 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq225 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq225
    | exact resolve eq225 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq225 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq225
    | (have j0 := eq225 X0 y
       grind)
    | exact resolve eq225 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq225
    | (have j0 := eq225 X0 (M.op x y)
       grind)
    | exact resolve eq225 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq644 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq64 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq64 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq64 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq64 X1 X1
       grind)
    | exact resolve eq13 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X1) (σ X0)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq14
    | (have j0 := eq14 (σ X1) (σ X0)
       have j1 := eq64 X0 X1
       grind)
    | (have r₁ := eq14 (σ X1) (σ X1)
       have r₂ := eq64 X1 X1
       grind)
    | (have r₁ := eq14 (σ X1) (σ X0)
       have r₂ := eq64 X0 X1
       grind)
    | (have r₁ := eq14 (σ X0) (σ X1)
       have r₂ := eq64 X0 X1
       grind)
    | exact resolve eq14 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq650 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq644 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq652 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq645 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq645 X1 X1
       have r₂ := eq14 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq645 X0 X1
       have r₂ := eq14 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq645 X0 X1
       have r₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq645 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq653 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq650 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq650 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
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
  have eq663 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq652
    | (have j0 := eq652 X0 X1
       grind)
    | exact resolve eq652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq664 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq3532 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (k (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ y) (σ X0)
       have j1 := eq91 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ X0)
       have r₂ := eq91 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq91 y
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq3536 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (k (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3532 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3532
  have eq3540 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (k (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3536 X0
       have j1 := eq13 (σ y) (σ X0)
       grind)
    | (have r₁ := eq3536 y
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq3536 X0
       have r₂ := eq13 (σ y) (σ X0)
       grind)
    | exact resolve eq3536 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3536
  have eq3561 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq3540
    | (have j0 := eq3540 X0
       grind)
    | exact resolve eq3540 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq3540
  have eq5449 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq664 (τ X1) (τ X0)
       have i₂ := eq394 X0 X1
       grind)
    | exact superpose eq394 eq664
    | (have j0 := eq664 (τ X0) (τ X1)
       grind)
    | exact resolve eq664 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq5627 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5449 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq5449
    | (have j0 := eq5449 X0 X1
       grind)
    | exact resolve eq5449 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5449
  have eq5711 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5627 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5627
    | (have j0 := eq5627 X0 X1
       grind)
    | exact resolve eq5627 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5627
  have eq5795 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5711 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq5711
    | (have j0 := eq5711 X0 X1
       grind)
    | exact resolve eq5711 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5711
  have eq5877 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5795 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5795
    | (have j0 := eq5795 X0 X1
       grind)
    | exact resolve eq5795 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5795
  have eq5959 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5877 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5877
    | (have j0 := eq5877 X0 X1
       grind)
    | exact resolve eq5877 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5877
  have eq6041 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5959 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5959
    | (have j0 := eq5959 X0 X1
       grind)
    | exact resolve eq5959 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5959
  have eq6050 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6041 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq6041
    | (have j0 := eq6041 X0 X1
       grind)
    | exact resolve eq6041 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6041
  have eq6057 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6050 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6050
    | (have j0 := eq6050 X0 X1
       grind)
    | exact resolve eq6050 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6050
  have eq7019 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq647 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq647
    | (have j0 := eq647 x y
       grind)
    | exact resolve eq647 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7088 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7019
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7019
    | exact resolve eq7019 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7019
  have eq7175 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7088
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7088
    | exact resolve eq7088 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7088
  have eq7260 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7175
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7175
    | exact resolve eq7175 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7175
  have eq7344 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq7260
    | exact resolve eq7260 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7260
  have eq7427 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7344
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7344
    | exact resolve eq7344 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7344
  have eq7509 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7427
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7427
    | exact resolve eq7427 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7427
  have eq7591 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq7509
    | exact resolve eq7509 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7509
  have eq7645 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq7591
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7591
    | exact resolve eq7591 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7591
  have eq7653 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7645
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7645
    | exact resolve eq7645 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7645
  have eq18528 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq81 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18529 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18528
    | exact resolve eq18528 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18528
  have eq18540 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq18529
       have r₂ := eq27
       grind)
    | exact resolve eq18529 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18529
  have eq18542 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18540
    | exact resolve eq18540 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18540
  have eq18544 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq18542
    | exact resolve eq18542 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18542
  have eq18548 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18544 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq18544
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq18544
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq18544
       grind)
    | exact resolve eq14 eq18544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18544
  have eq18549 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq18548
  have eq18560 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18549 eq55
    | exact resolve eq55 eq18549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18549
  have eq18585 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq18560
    | exact resolve eq18560 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18560
  have eq18588 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq18585
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq18585
       have r₂ := eq14 y x
       grind)
    | (have r₁ := eq18585
       have r₂ := eq14 x y
       grind)
    | exact resolve eq18585 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18585
  have eq18606 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq646 x y
       have i₂ := eq18588
       grind)
    | exact superpose eq18588 eq646
    | (have j0 := eq646 x y
       grind)
    | exact resolve eq646 eq18588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq18609 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18588
       grind)
    | exact superpose eq18588 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18588
  have eq18610 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18609
  have eq18612 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18606
  have eq18614 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18610
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18610
    | exact resolve eq18610 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18610
  have eq18615 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18614
  have eq18618 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18612
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18612
    | exact resolve eq18612 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18612
  have eq18631 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18615
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18615
    | exact resolve eq18615 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18615
  have eq18632 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18631
  have eq18635 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18618
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18618
    | exact resolve eq18618 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18618
  have eq18641 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18635
    | exact resolve eq18635 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18635
  have eq18642 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18641
  have eq18646 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18642
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18642
    | exact resolve eq18642 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18642
  have eq18650 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18646
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18646
    | exact resolve eq18646 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18646
  have eq18655 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18650
    | exact resolve eq18650 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18650
  have eq18656 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18655
  have eq18661 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18656
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18656
    | exact resolve eq18656 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18656
  have eq18665 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18661
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18661
    | exact resolve eq18661 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18661
  have eq18715 : y ≠ y ∨ x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18632
       grind)
    | exact superpose eq18632 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq18632
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq18632
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq18632
       grind)
    | exact resolve eq12 eq18632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18632
  have eq18719 : x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18715
  have eq18722 : x = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18719
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18719
    | exact resolve eq18719 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18719
  have eq18723 : x = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18722
  have eq18724 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18723
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18723
    | exact resolve eq18723 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18723
  have eq18732 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18665 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq18665
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq18665
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq18665
       grind)
    | exact resolve eq12 eq18665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18665
  have eq18736 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18732
  have eq18739 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18736
    | exact resolve eq18736 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18736
  have eq18740 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18739
  have eq18741 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18740
    | exact resolve eq18740 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18740
  have eq19808 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18724
       grind)
    | exact superpose eq18724 eq88
    | exact resolve eq88 eq18724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18724
  have eq19836 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq19808
    | exact resolve eq19808 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19808
  have eq20167 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19836 eq18741
    | exact resolve eq18741 eq19836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18741 eq19836
  have eq20174 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq20167
  have eq20176 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq20174
       have r₂ := eq27
       grind)
    | exact resolve eq20174 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20174
  have eq20187 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20176 eq57
    | (have r₁ := eq57
       have r₂ := eq20176
       grind)
    | exact resolve eq57 eq20176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20189 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20176 eq27
    | exact resolve eq27 eq20176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20176
  have eq20191 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq20187
  have eq53714 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20191 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq20191
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq20191
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq20191
       grind)
    | exact resolve eq14 eq20191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20191
  have eq53715 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq53714
  have eq62512 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq53715 eq81
    | exact resolve eq81 eq53715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq53715
  have eq62545 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq62512
  have eq62554 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq62545
       have r₂ := eq20189
       grind)
    | exact resolve eq62545 eq20189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20189 eq62545
  have eq90036 : (τ (σ x)) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq62554 eq55
    | exact resolve eq55 eq62554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq62554
  have eq90230 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq90036
    | exact resolve eq90036 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90036
  have eq90237 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq90230
       have r₂ := eq56
       grind)
    | exact resolve eq90230 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90230
  have eq90947 : y ≠ y ∨ x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq90237
       grind)
    | exact superpose eq90237 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq90237
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq90237
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq90237
       grind)
    | exact resolve eq12 eq90237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90949 : y ≠ y ∨ y = (k x y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq90237
       grind)
    | exact superpose eq90237 eq14
    | (have j0 := eq14 x y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq90237
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq90237
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq90237
       grind)
    | exact resolve eq14 eq90237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90237
  have eq90950 : y = (k x y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq90949
  have eq90951 : y ≠ y ∨ x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq90947
  have eq90952 : x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq90951
  have eq90953 : x = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90952
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90952
    | exact resolve eq90952 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90952
  have eq90954 : x = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq90953
  have eq90955 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = y ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90954
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90954
    | exact resolve eq90954 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90954
  have eq90956 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq90950
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq90950
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq90950 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90978 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq664 x y
       have i₂ := eq90950
       grind)
    | exact superpose eq90950 eq664
    | (have j0 := eq664 x y
       grind)
    | exact resolve eq664 eq90950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90950
  have eq90983 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq90978
  have eq90991 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by grind
  clear eq90956
  have eq90993 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq90983
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq90983
    | exact resolve eq90983 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90983
  have eq91009 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq90991
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90991
    | exact resolve eq90991 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90991
  have eq91011 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq90993
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq90993
    | exact resolve eq90993 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90993
  have eq91012 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq91011
  have eq91015 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq91009
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91009
    | exact resolve eq91009 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91009
  have eq91016 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq91015
  have eq91017 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq91012
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq91012
    | exact resolve eq91012 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91012
  have eq91019 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq91017
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq91017
    | exact resolve eq91017 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91017
  have eq91021 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq91019
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq91019
    | exact resolve eq91019 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91019
  have eq91023 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq91021
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq91021
    | exact resolve eq91021 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91021
  have eq91026 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq91023
    | exact resolve eq91023 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91023
  have eq91027 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq91026
  have eq91030 : y ≠ y ∨ x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq91016
       grind)
    | exact superpose eq91016 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq91016
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq91016
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq91016
       grind)
    | exact resolve eq12 eq91016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91032 : y ≠ y ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq91016
       grind)
    | exact superpose eq91016 eq14
    | (have j0 := eq14 x y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq91016
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq91016
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq91016
       grind)
    | exact resolve eq14 eq91016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91016
  have eq91033 : y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq91032
  have eq91034 : y ≠ y ∨ x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq91030
  have eq91035 : x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq91034
  have eq91036 : x = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91035
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91035
    | exact resolve eq91035 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91035
  have eq91037 : x = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq91036
  have eq91038 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq91037
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91037
    | exact resolve eq91037 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91037
  have eq91750 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq664 x y
       have i₂ := eq91033
       grind)
    | exact superpose eq91033 eq664
    | (have j0 := eq664 x y
       grind)
    | exact resolve eq664 eq91033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91033
  have eq91754 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq91750
  have eq91764 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91754
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq91754
    | exact resolve eq91754 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91754
  have eq91781 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91764
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq91764
    | exact resolve eq91764 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91764
  have eq91782 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq91781
  have eq91785 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91782
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq91782
    | exact resolve eq91782 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91782
  have eq91787 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91785
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq91785
    | exact resolve eq91785 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91785
  have eq91788 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91787
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq91787
    | exact resolve eq91787 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91787
  have eq91789 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91788
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq91788
    | exact resolve eq91788 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91788
  have eq91790 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq91789
    | exact resolve eq91789 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91789
  have eq91791 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq91790
  have eq91795 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq88
       have i₂ := eq91038
       grind)
    | exact superpose eq91038 eq88
    | exact resolve eq88 eq91038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91038
  have eq91889 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq91795
    | exact resolve eq91795 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91795
  have eq91979 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq91791 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq91791
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq91791
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq91791
       grind)
    | exact resolve eq12 eq91791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91791
  have eq91983 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq91979
  have eq91984 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq91983
  have eq91985 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq91984
    | exact resolve eq91984 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91984
  have eq91986 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq91985
  have eq91987 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq91986
    | exact resolve eq91986 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91986
  have eq92157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq91987 eq91889
    | exact resolve eq91889 eq91987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91889 eq91987
  have eq92164 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq92157
  have eq92206 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq92164
       have r₂ := eq27
       grind)
    | exact resolve eq92164 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92164
  have eq92210 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92206 eq51
    | (have r₁ := eq51
       have r₂ := eq92206
       grind)
    | exact resolve eq51 eq92206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92206
  have eq92215 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq92210
  have eq93018 : (τ (σ x)) = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92215 eq98
    | exact resolve eq98 eq92215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92215
  have eq93103 : x = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq93018
    | exact resolve eq93018 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93018
  have eq93110 : x = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq93103
       have r₂ := eq50
       grind)
    | exact resolve eq93103 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93103
  have eq93918 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq93110
       grind)
    | exact superpose eq93110 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq93110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93919 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq93918
  have eq93945 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq93919
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93919
    | exact resolve eq93919 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93919
  have eq131036 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq88
       have i₂ := eq90955
       grind)
    | exact superpose eq90955 eq88
    | exact resolve eq88 eq90955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90955
  have eq131194 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq131036
    | exact resolve eq131036 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131036
  have eq132160 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq91027 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq91027
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq91027
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq91027
       grind)
    | exact resolve eq12 eq91027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91027
  have eq132164 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq132160
  have eq132165 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq132164
  have eq132166 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq26 eq132165
    | exact resolve eq132165 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132165
  have eq132167 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq132166
  have eq132168 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq26 eq132167
    | exact resolve eq132167 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132167
  have eq133295 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq132168 eq131194
    | exact resolve eq131194 eq132168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131194 eq132168
  have eq133302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq133295
  have eq133372 : x = (k x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq133302
       have r₂ := eq27
       grind)
    | exact resolve eq133302 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133302
  have eq133402 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq133372
       grind)
    | exact superpose eq133372 eq44
    | exact resolve eq44 eq133372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133486 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq663 x y
       have i₂ := eq133372
       grind)
    | exact superpose eq133372 eq663
    | (have j0 := eq663 x y
       grind)
    | exact resolve eq663 eq133372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq133372
  have eq133489 : (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq133486
  have eq133567 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq133489
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq133489
    | exact resolve eq133489 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133489
  have eq133583 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq133402
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq133402
    | exact resolve eq133402 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133402
  have eq133588 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq133567
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq133567
    | exact resolve eq133567 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133567
  have eq133593 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq133588
       have r₂ := eq51
       grind)
    | exact resolve eq133588 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133588
  have eq133596 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq133593
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq133593
    | exact resolve eq133593 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133593
  have eq133600 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq133596
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq133596
    | exact resolve eq133596 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133596
  have eq133603 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq133600
    | exact resolve eq133600 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133600
  have eq133607 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq133603
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq133603
    | exact resolve eq133603 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133603
  have eq133610 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq133607
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq133607
    | exact resolve eq133607 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133607
  have eq136764 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq133610 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq133610
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq133610
       grind)
    | exact resolve eq14 eq133610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133610
  have eq136765 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq136764
  have eq136774 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq133583 eq136765
    | exact resolve eq136765 eq133583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136765
  have eq136838 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq136774
  have eq136853 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq136838
       have r₂ := eq51
       grind)
    | exact resolve eq136838 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136838
  have eq136869 : (τ (σ x)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq136853 eq98
    | exact resolve eq98 eq136853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136853
  have eq136967 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq136869
    | exact resolve eq136869 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136869
  have eq136974 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq136967
       have r₂ := eq50
       grind)
    | exact resolve eq136967 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136967
  have eq136981 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq136974
       grind)
    | exact superpose eq136974 eq88
    | exact resolve eq88 eq136974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137017 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq664 y x
       have i₂ := eq136974
       grind)
    | exact superpose eq136974 eq664
    | (have j0 := eq664 y x
       grind)
    | exact resolve eq664 eq136974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq136974
  have eq137021 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq137017
  have eq137052 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq137021
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq137021
    | exact resolve eq137021 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137021
  have eq137068 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq136981
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq136981
    | exact resolve eq136981 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136981
  have eq137072 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq137052
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq137052
    | exact resolve eq137052 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137052
  have eq137073 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq137072
  have eq137076 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq137073
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq137073
    | exact resolve eq137073 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137073
  have eq137078 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq137076
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq137076
    | exact resolve eq137076 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137076
  have eq137080 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq137078
    | exact resolve eq137078 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137078
  have eq137082 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq137080
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq137080
    | exact resolve eq137080 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137080
  have eq137084 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq137082
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq137082
    | exact resolve eq137082 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137082
  have eq137424 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq137084 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq137084
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq137084
       grind)
    | exact resolve eq12 eq137084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137084
  have eq137428 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq137424
  have eq137429 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq137428
  have eq137430 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq137429
    | exact resolve eq137429 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137429
  have eq137431 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq137430
  have eq137432 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq137431
    | exact resolve eq137431 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137431
  have eq137619 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq137432 eq137068
    | exact resolve eq137068 eq137432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137068 eq137432
  have eq137626 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq137619
  have eq137723 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq137626 eq27
    | exact resolve eq27 eq137626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137725 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq137626 eq57
    | (have r₁ := eq57
       have r₂ := eq137626
       grind)
    | exact resolve eq57 eq137626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq137626
  have eq137735 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq137725
  have eq138646 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq137735 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq137735
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq137735
       grind)
    | exact resolve eq12 eq137735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137735
  have eq138650 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq138646
  have eq138651 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq138650
  have eq138652 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq138651
    | exact resolve eq138651 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138651
  have eq138653 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq138652
  have eq138654 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq138653
    | exact resolve eq138653 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138653
  have eq154505 : y ≠ y ∨ x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq93945
       grind)
    | exact superpose eq93945 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq93945
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq93945
       grind)
    | exact resolve eq12 eq93945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93945
  have eq154510 : y ≠ y ∨ x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq154505
  have eq154511 : x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq154510
  have eq154512 : x = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq154511
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq154511
    | exact resolve eq154511 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154511
  have eq154513 : x = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq154512
  have eq154514 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq154513
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq154513
    | exact resolve eq154513 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154513
  have eq157388 : x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq93110
       have i₂ := eq154514
       grind)
    | exact superpose eq154514 eq93110
    | exact resolve eq93110 eq154514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154514
  have eq157484 : x = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq157388
  have eq157600 : x ≠ x ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq157484
       grind)
    | exact superpose eq157484 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq157484
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq157484
       grind)
    | exact resolve eq13 eq157484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157484
  have eq157602 : x = (M.op x y) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq157600
  have eq157613 : x = (M.op x y) ∨ y = (k y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq157602
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq157602
    | exact resolve eq157602 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157602
  have eq157614 : y = (k y x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq157613
  have eq157681 : x = y ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq93110
       have i₂ := eq157614
       grind)
    | exact superpose eq157614 eq93110
    | exact resolve eq93110 eq157614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93110 eq157614
  have eq157781 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq157681
  have eq157895 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq157781 eq29
    | exact resolve eq29 eq157781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157781
  have eq158267 : x = y ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq157895
    | exact resolve eq157895 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157895
  have eq158268 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq158267
  have eq158269 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq158268 eq20
    | exact resolve eq20 eq158268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158270 : (σ (k x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq158268 eq45
    | exact resolve eq45 eq158268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq158272 : y ≠ y ∨ y = (M.op y x) ∨ x = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq158268 eq56
    | (have r₁ := eq56
       have r₂ := eq158268
       grind)
    | exact resolve eq56 eq158268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq158331 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq158268 eq411
    | exact resolve eq411 eq158268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq158268
  have eq158421 : y = (M.op y x) ∨ x = (k x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq158272
  have eq158495 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (k X0 (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq158331 X0
       have i₂ := eq410 X0
       grind)
    | exact superpose eq410 eq158331
    | exact resolve eq158331 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq158331
  have eq158552 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq158270
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq158270
    | exact resolve eq158270 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq158270
  have eq158553 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq158269
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq158269
    | exact resolve eq158269 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158269
  have eq159586 : (σ x) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq158553 eq7653
    | exact resolve eq7653 eq158553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7653
  have eq159805 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq158553 eq137723
    | (have r₁ := eq137723
       have r₂ := eq158553
       grind)
    | exact resolve eq137723 eq158553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137723 eq158553
  have eq159864 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq159805
  have eq159865 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq159864
  have eq160130 : (σ x) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq159586
       have r₂ := eq27
       grind)
    | exact resolve eq159586 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159586
  have eq161144 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq159865 eq51
    | (have r₁ := eq51
       have r₂ := eq159865
       grind)
    | exact resolve eq51 eq159865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159865
  have eq161148 : (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq161144
  have eq165507 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq158552 eq133583
    | exact resolve eq133583 eq158552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158552
  have eq165531 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq165507
  have eq179456 : (τ (σ x)) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq161148 eq98
    | exact resolve eq98 eq161148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161148
  have eq179583 : x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq179456
    | exact resolve eq179456 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179456
  have eq179587 : x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq179583
       have r₂ := eq50
       grind)
    | exact resolve eq179583 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179583
  have eq181843 : (τ (σ x)) = (τ (k (σ x) (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq133583 eq158495
    | exact resolve eq158495 eq133583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133583 eq158495
  have eq182256 : (τ (σ x)) = (τ (k (σ x) (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq181843
  have eq182582 : (τ (σ x)) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq61 eq182256
    | exact resolve eq182256 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182256
  have eq182596 : x = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq182582
    | exact resolve eq182582 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182582
  have eq222787 : y ≠ y ∨ x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq158421
       grind)
    | exact superpose eq158421 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq158421
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq158421
       grind)
    | exact resolve eq12 eq158421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158421
  have eq222791 : y ≠ y ∨ x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq222787
  have eq222792 : x = y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq222791
  have eq222795 : x = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq222792
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq222792
    | exact resolve eq222792 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222792
  have eq222796 : x = (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = (k x y) := by grind
  clear eq222795
  have eq222797 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq222796
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq222796
    | exact resolve eq222796 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222796
  have eq228191 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq179587
       have i₂ := eq222797
       grind)
    | exact superpose eq222797 eq179587
    | exact resolve eq179587 eq222797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222797
  have eq228210 : x = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq228191
  have eq830283 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq165531 eq160130
    | (have r₁ := eq160130
       have r₂ := eq165531
       grind)
    | exact resolve eq160130 eq165531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160130 eq165531
  have eq830302 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq830283
  have eq830303 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq830302
  have eq830310 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq830303 eq14
    | (have j0 := eq14 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq14 (σ x) (σ (M.op x y))
       have r₂ := eq830303
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq830303
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq830303
       grind)
    | exact resolve eq14 eq830303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830303
  have eq830311 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq830310
  have eq830719 : (τ (σ (M.op x y))) = (k x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq830311 eq61
    | exact resolve eq61 eq830311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq830311
  have eq830845 : (M.op x y) = (k x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30 eq830719
    | exact resolve eq830719 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830719
  have eq830919 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq830845 eq182596
    | exact resolve eq182596 eq830845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182596 eq830845
  have eq831058 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq830919
  have eq831268 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq831058 eq51
    | (have r₁ := eq51
       have r₂ := eq831058
       grind)
    | exact resolve eq51 eq831058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831058
  have eq831276 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq831268
  have eq832195 : (τ (σ x)) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq831276 eq98
    | exact resolve eq98 eq831276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq831276
  have eq832428 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq832195
    | exact resolve eq832195 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832195
  have eq832439 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq832428
       have r₂ := eq50
       grind)
    | exact resolve eq832428 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq832428
  have eq832452 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq832439
       grind)
    | exact superpose eq832439 eq88
    | exact resolve eq88 eq832439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq832557 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3561 x
       have i₂ := eq832439
       grind)
    | exact superpose eq832439 eq3561
    | (have j0 := eq3561 x
       grind)
    | exact resolve eq3561 eq832439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3561 eq832439
  have eq832584 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq832557
  have eq832656 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq832584
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq832584
    | exact resolve eq832584 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832584
  have eq832657 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq832656
  have eq832721 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq832452
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq832452
    | exact resolve eq832452 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832452
  have eq832739 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq832657
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq832657
    | exact resolve eq832657 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832657
  have eq832760 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq832739
    | exact resolve eq832739 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832739
  have eq832778 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq832760
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq832760
    | exact resolve eq832760 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832760
  have eq832877 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq832721 eq138654
    | exact resolve eq138654 eq832721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138654 eq832721
  have eq832996 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq832877
  have eq835920 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq832778 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq832778
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq832778
       grind)
    | exact resolve eq14 eq832778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832778
  have eq835921 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq835920
  have eq840013 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq835921 eq832996
    | exact resolve eq832996 eq835921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832996 eq835921
  have eq840076 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq840013
  have eq840182 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq840076 eq27
    | exact resolve eq27 eq840076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840076
  have eq2262276 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq6057 y x
       have i₂ := eq179587
       grind)
    | exact superpose eq179587 eq6057
    | (have j0 := eq6057 y x
       grind)
    | (have r₁ := eq6057 y x
       have r₂ := eq179587
       grind)
    | exact resolve eq6057 eq179587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6057 eq179587
  have eq2262905 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2262276
  have eq2262906 : x = (M.op x y) ∨ x = y ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2262905
  have eq2262979 : y = (M.op y x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2262906
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2262906
    | exact resolve eq2262906 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262906
  have eq2263025 : y ≠ y ∨ y = (k x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq2262979
       grind)
    | exact superpose eq2262979 eq14
    | (have j0 := eq14 x y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq2262979
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq2262979
       grind)
    | exact resolve eq14 eq2262979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262979
  have eq2263026 : y = (k x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2263025
  have eq2263142 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq228210
       have i₂ := eq2263026
       grind)
    | exact superpose eq2263026 eq228210
    | exact resolve eq228210 eq2263026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228210 eq2263026
  have eq2263323 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2263142
  have eq2263598 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2263323 eq28
    | exact resolve eq28 eq2263323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263323
  have eq2265162 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2263598
    | exact resolve eq2263598 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263598
  have eq2265163 : x = (M.op x y) ∨ x = y := by grind
  clear eq2265162
  have eq2265165 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2265163 eq20
    | exact resolve eq20 eq2265163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2266362 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2265165
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2265165
    | exact resolve eq2265165 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265165
  have eq2267104 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2266362 eq840182
    | (have r₁ := eq840182
       have r₂ := eq2266362
       grind)
    | exact resolve eq840182 eq2266362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840182 eq2266362
  have eq2267237 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq2267104
  have eq2267238 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq2267237
  have eq2267854 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq2267238 eq29
    | exact resolve eq29 eq2267238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2267238
  have eq2270046 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq2267854
    | exact resolve eq2267854 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2267854
  have eq2271211 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2270046 eq2265163
    | exact resolve eq2265163 eq2270046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265163 eq2270046
  have eq2271212 : x = y := by grind
  clear eq2271211
  have eq2272327 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2271212
       grind)
    | exact superpose eq2271212 eq18
    | exact resolve eq18 eq2271212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2272328 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2271212
       grind)
    | exact superpose eq2271212 eq24
    | exact resolve eq24 eq2271212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2271212
  have eq2273658 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2272328
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2272328
    | exact resolve eq2272328 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2272328
  have eq2273661 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2273658 eq26
    | exact resolve eq26 eq2273658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2275553 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq2272327
       grind)
    | exact superpose eq2272327 eq74
    | exact resolve eq74 eq2272327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq2275566 : x ≠ (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq2272327
       grind)
    | exact superpose eq2272327 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq2272327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2272327
  have eq2275591 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2275553
    | exact resolve eq2275553 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275553
  have eq2276006 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2275591 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq2275591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2276033 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2276006
  have eq2276043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2273661 eq2276033
    | exact resolve eq2276033 eq2273661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276033
  have eq2276095 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2276043
       have r₂ := eq27
       grind)
    | exact resolve eq2276043 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276043
  have eq2276116 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2273661 eq2276095
    | exact resolve eq2276095 eq2273661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276095
  have eq2276138 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2276116 eq27
    | exact resolve eq27 eq2276116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2276139 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2276116 eq51
    | (have r₁ := eq51
       have r₂ := eq2276116
       grind)
    | exact resolve eq51 eq2276116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2276116
  have eq2276146 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2276139
  have eq2276151 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2273658 eq2276146
    | exact resolve eq2276146 eq2273658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2273658 eq2276146
  have eq2276772 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2276151 eq49
    | exact resolve eq49 eq2276151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq2276816 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2276151 eq2275591
    | exact resolve eq2275591 eq2276151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275591 eq2276151
  have eq2276850 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2276816
  have eq2276864 : x = (M.op x y) := by
    first
    | (have r₁ := eq2276850
       have r₂ := eq2276138
       grind)
    | exact resolve eq2276850 eq2276138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276138 eq2276850
  have eq2276906 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq2276772
    | exact resolve eq2276772 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2276772
  have eq2276931 : x = (k x x) := by
    first
    | (have r₁ := eq2276906
       have r₂ := eq2275566
       grind)
    | exact resolve eq2276906 eq2275566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275566 eq2276906
  have eq2276949 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2276864 eq20
    | exact resolve eq20 eq2276864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2276864
  have eq2278156 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2276949
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2276949
    | exact resolve eq2276949 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276949
  have eq2283489 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq647 x x
       have i₂ := eq2276931
       grind)
    | exact superpose eq2276931 eq647
    | (have j0 := eq647 x x
       grind)
    | exact resolve eq647 eq2276931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq2276931
  have eq2283501 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2283489
  have eq2283502 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2283501
  have eq2283528 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2283502
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2283502
    | exact resolve eq2283502 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2283502
  have eq2283632 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2273661 eq2283528
    | exact resolve eq2283528 eq2273661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2273661 eq2283528
  have eq2283725 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2278156 eq2283632
    | exact resolve eq2283632 eq2278156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2278156 eq2283632
  have eq2283814 : False := by grind
  exact eq2283814

/-- `x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else if X = Y then m(X,X)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyx_y_pyx_x_x_y_x_y_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
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
  have eq29 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X1
    grind
  have eq30 : x = (τ (σ x)) := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  clear eq37
  have eq51 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : x ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq29 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq29
    | (have j0 := eq29 (σ X0)
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq29 x
       grind)
    | exact superpose eq29 eq45
    | (have j1 := eq29 x
       grind)
    | exact resolve eq45 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq68 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq94
    | exact resolve eq94 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq491 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq58 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq681 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq83 X1 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq14 (σ X0) (σ X0)
       have r₂ := eq83 X0 X0
       grind)
    | (have r₁ := eq14 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq14 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq685 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq682 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq682 X0 X0
       have r₂ := eq14 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq682 X0 X1
       have r₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq682 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq686 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq681 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq681 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq681 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | exact resolve eq681 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq695 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq685 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq685
    | (have j0 := eq685 X0 X1
       grind)
    | exact resolve eq685 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq696 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq686 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq686
    | (have j0 := eq686 X0 X1
       grind)
    | exact resolve eq686 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq697 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq696 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq13933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq13934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq13933
    | exact resolve eq13933 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13933
  have eq13945 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq13934
       have r₂ := eq28
       grind)
    | exact resolve eq13934 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13934
  have eq13947 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq13945
    | exact resolve eq13945 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13945
  have eq13949 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq13947
    | exact resolve eq13947 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13947
  have eq13951 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13949 eq69
    | (have r₁ := eq69
       have r₂ := eq13949
       grind)
    | exact resolve eq69 eq13949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq13949
  have eq13955 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13951
  have eq13956 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13955
  have eq13962 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13956 eq82
    | exact resolve eq82 eq13956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13956
  have eq13989 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq13962
    | exact resolve eq13962 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13962
  have eq13995 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq13989
       have r₂ := eq68
       grind)
    | exact resolve eq13989 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13989
  have eq14010 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq13995
       grind)
    | exact superpose eq13995 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq13995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13995
  have eq14011 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14010
  have eq14016 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14011
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14011
    | exact resolve eq14011 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14011
  have eq14017 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14016
  have eq14031 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14017
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14017
    | exact resolve eq14017 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14017
  have eq14048 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14031 eq53
    | (have r₁ := eq53
       have r₂ := eq14031
       grind)
    | exact resolve eq53 eq14031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14031
  have eq14050 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14048
  have eq14109 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14050 eq82
    | exact resolve eq82 eq14050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq14050
  have eq14141 : y = (k y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq14109
    | exact resolve eq14109 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14109
  have eq14146 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14141
       have r₂ := eq52
       grind)
    | exact resolve eq14141 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq14141
  have eq14162 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq697 y x
       have i₂ := eq14146
       grind)
    | exact superpose eq14146 eq697
    | (have j0 := eq697 x y
       grind)
    | exact resolve eq697 eq14146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq14163 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq14146
       grind)
    | exact superpose eq14146 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq14146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14146
  have eq14164 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14163
  have eq14165 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14162
  have eq14166 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14165
  have eq14171 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14164
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14164
    | exact resolve eq14164 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14164
  have eq14172 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq14171
  have eq14173 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14166
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14166
    | exact resolve eq14166 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14166
  have eq14186 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14172
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14172
    | exact resolve eq14172 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14172
  have eq14187 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14173
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14173
    | exact resolve eq14173 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14173
  have eq14188 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq14187
  have eq14191 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14188
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14188
    | exact resolve eq14188 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14188
  have eq14193 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14191
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14191
    | exact resolve eq14191 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14191
  have eq14195 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14193
    | exact resolve eq14193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14193
  have eq14202 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14186 eq31
    | exact resolve eq31 eq14186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14186
  have eq14318 : x = y ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq14202
    | exact resolve eq14202 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14202
  have eq14319 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq14318
  have eq14321 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14319 eq21
    | exact resolve eq21 eq14319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14325 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14319 eq68
    | (have r₁ := eq68
       have r₂ := eq14319
       grind)
    | exact resolve eq68 eq14319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq14319
  have eq14386 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq14325
  have eq14387 : x = (k y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq14386
  have eq14448 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14321
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14321
    | exact resolve eq14321 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14321
  have eq14597 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq695 y x
       have i₂ := eq14387
       grind)
    | exact superpose eq14387 eq695
    | (have j0 := eq695 y x
       grind)
    | exact resolve eq695 eq14387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq14387
  have eq14600 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq14597
  have eq14601 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq14600
  have eq14608 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14601
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14601
    | exact resolve eq14601 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14601
  have eq14622 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14608
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14608
    | exact resolve eq14608 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14608
  have eq14625 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14622
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14622
    | exact resolve eq14622 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14622
  have eq14627 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14625
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14625
    | exact resolve eq14625 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14625
  have eq14629 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq14627
    | exact resolve eq14627 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14627
  have eq14751 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq14195 eq28
    | exact resolve eq28 eq14195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14195
  have eq14766 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14629 eq28
    | exact resolve eq28 eq14629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14629
  have eq14780 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14766
       have r₂ := eq14448
       grind)
    | exact resolve eq14766 eq14448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14448 eq14766
  have eq14783 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14780 eq31
    | exact resolve eq31 eq14780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14780
  have eq14904 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq14783
    | exact resolve eq14783 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14783
  have eq14905 : x = (M.op x y) ∨ x = y := by grind
  clear eq14904
  have eq14907 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14905 eq21
    | exact resolve eq21 eq14905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15032 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14907
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14907
    | exact resolve eq14907 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14907
  have eq15101 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15032 eq14751
    | (have r₁ := eq14751
       have r₂ := eq15032
       grind)
    | exact resolve eq14751 eq15032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14751 eq15032
  have eq15102 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq15101
  have eq15103 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq15102
  have eq15366 : y = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq15103 eq31
    | exact resolve eq31 eq15103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq15103
  have eq15508 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq15366
    | exact resolve eq15366 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq15366
  have eq15509 : y = (M.op x y) ∨ x = y := by grind
  clear eq15508
  have eq15576 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15509 eq14905
    | exact resolve eq14905 eq15509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14905 eq15509
  have eq15579 : x = y := by grind
  clear eq15576
  have eq15645 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15579
       grind)
    | exact superpose eq15579 eq19
    | exact resolve eq19 eq15579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq15646 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq15579
       grind)
    | exact superpose eq15579 eq25
    | exact resolve eq25 eq15579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15579
  have eq15768 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15646
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15646
    | exact resolve eq15646 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15646
  have eq15771 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15768 eq27
    | exact resolve eq27 eq15768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq15896 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60
       have i₂ := eq15645
       grind)
    | exact superpose eq15645 eq60
    | exact resolve eq60 eq15645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq15898 : x ≠ (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq15645
       grind)
    | exact superpose eq15645 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq15645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15645
  have eq15899 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq15896
    | exact resolve eq15896 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15896
  have eq15921 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15899 eq29
    | (have j0 := eq29 (σ x)
       grind)
    | exact resolve eq29 eq15899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq15922 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15771 eq15921
    | exact resolve eq15921 eq15771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15921
  have eq15935 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15922
       have r₂ := eq28
       grind)
    | exact resolve eq15922 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15922
  have eq15939 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15771 eq15935
    | exact resolve eq15935 eq15771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15935
  have eq15945 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15939 eq28
    | exact resolve eq28 eq15939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15946 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15939 eq53
    | (have r₁ := eq53
       have r₂ := eq15939
       grind)
    | exact resolve eq53 eq15939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq15939
  have eq15949 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15946
  have eq15953 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15768 eq15949
    | exact resolve eq15949 eq15768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15768 eq15949
  have eq16365 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15953 eq51
    | exact resolve eq51 eq15953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq16373 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15953 eq15899
    | exact resolve eq15899 eq15953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15899 eq15953
  have eq16380 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq16373
  have eq16386 : x = (M.op x y) := by
    first
    | (have r₁ := eq16380
       have r₂ := eq15945
       grind)
    | exact resolve eq16380 eq15945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15945 eq16380
  have eq16394 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq16365
    | exact resolve eq16365 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16365
  have eq16401 : x = (k x x) := by
    first
    | (have r₁ := eq16394
       have r₂ := eq15898
       grind)
    | exact resolve eq16394 eq15898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15898 eq16394
  have eq16405 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq16386 eq21
    | exact resolve eq21 eq16386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16386
  have eq16538 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16405
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16405
    | exact resolve eq16405 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16405
  have eq16764 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq491 x
       have i₂ := eq16401
       grind)
    | exact superpose eq16401 eq491
    | (have j0 := eq491 x
       grind)
    | exact resolve eq491 eq16401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq16401
  have eq16767 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq16764
  have eq16773 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16767
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16767
    | exact resolve eq16767 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq16767
  have eq16785 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15771 eq16773
    | exact resolve eq16773 eq15771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15771 eq16773
  have eq16795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16538 eq16785
    | exact resolve eq16785 eq16538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16538 eq16785
  have eq16804 : False := by grind
  exact eq16804

/-- `x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else if X = Y then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyx_y_pyx_x_x_y_x_y_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
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
  have eq29 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X1
    grind
  have eq30 : x = (τ (σ x)) := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  clear eq37
  have eq51 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : x ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq29 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq29
    | (have j0 := eq29 (σ X0)
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq29 x
       grind)
    | exact superpose eq29 eq45
    | (have j1 := eq29 x
       grind)
    | exact resolve eq45 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq68 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq94
    | exact resolve eq94 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq491 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq58 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq681 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq83 X1 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq14 (σ X0) (σ X0)
       have r₂ := eq83 X0 X0
       grind)
    | (have r₁ := eq14 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq14 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq685 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq682 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq682 X0 X0
       have r₂ := eq14 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq682 X0 X1
       have r₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq682 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq686 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq681 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq681 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq681 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | exact resolve eq681 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq695 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq685 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq685
    | (have j0 := eq685 X0 X1
       grind)
    | exact resolve eq685 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq696 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq686 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq686
    | (have j0 := eq686 X0 X1
       grind)
    | exact resolve eq686 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq697 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq696 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq13933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq13934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq13933
    | exact resolve eq13933 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13933
  have eq13945 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq13934
       have r₂ := eq28
       grind)
    | exact resolve eq13934 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13934
  have eq13947 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq13945
    | exact resolve eq13945 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13945
  have eq13949 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq13947
    | exact resolve eq13947 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13947
  have eq13951 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13949 eq69
    | (have r₁ := eq69
       have r₂ := eq13949
       grind)
    | exact resolve eq69 eq13949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq13949
  have eq13955 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13951
  have eq13956 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13955
  have eq13962 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13956 eq82
    | exact resolve eq82 eq13956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13956
  have eq13989 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq13962
    | exact resolve eq13962 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13962
  have eq13995 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq13989
       have r₂ := eq68
       grind)
    | exact resolve eq13989 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13989
  have eq14010 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq13995
       grind)
    | exact superpose eq13995 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq13995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13995
  have eq14011 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14010
  have eq14016 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14011
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14011
    | exact resolve eq14011 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14011
  have eq14017 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14016
  have eq14031 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14017
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14017
    | exact resolve eq14017 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14017
  have eq14048 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14031 eq53
    | (have r₁ := eq53
       have r₂ := eq14031
       grind)
    | exact resolve eq53 eq14031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14031
  have eq14050 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14048
  have eq14109 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14050 eq82
    | exact resolve eq82 eq14050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq14050
  have eq14141 : y = (k y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq14109
    | exact resolve eq14109 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14109
  have eq14146 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14141
       have r₂ := eq52
       grind)
    | exact resolve eq14141 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq14141
  have eq14162 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq697 y x
       have i₂ := eq14146
       grind)
    | exact superpose eq14146 eq697
    | (have j0 := eq697 x y
       grind)
    | exact resolve eq697 eq14146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq14163 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq14146
       grind)
    | exact superpose eq14146 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq14146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14146
  have eq14164 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14163
  have eq14165 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14162
  have eq14166 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14165
  have eq14171 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14164
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14164
    | exact resolve eq14164 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14164
  have eq14172 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq14171
  have eq14173 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14166
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14166
    | exact resolve eq14166 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14166
  have eq14186 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14172
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14172
    | exact resolve eq14172 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14172
  have eq14187 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14173
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14173
    | exact resolve eq14173 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14173
  have eq14188 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq14187
  have eq14191 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14188
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14188
    | exact resolve eq14188 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14188
  have eq14193 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14191
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14191
    | exact resolve eq14191 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14191
  have eq14195 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14193
    | exact resolve eq14193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14193
  have eq14202 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14186 eq31
    | exact resolve eq31 eq14186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14186
  have eq14318 : x = y ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq14202
    | exact resolve eq14202 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14202
  have eq14319 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq14318
  have eq14321 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14319 eq21
    | exact resolve eq21 eq14319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14325 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14319 eq68
    | (have r₁ := eq68
       have r₂ := eq14319
       grind)
    | exact resolve eq68 eq14319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq14319
  have eq14386 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq14325
  have eq14387 : x = (k y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq14386
  have eq14448 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14321
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14321
    | exact resolve eq14321 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14321
  have eq14597 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq695 y x
       have i₂ := eq14387
       grind)
    | exact superpose eq14387 eq695
    | (have j0 := eq695 y x
       grind)
    | exact resolve eq695 eq14387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq14387
  have eq14600 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq14597
  have eq14601 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq14600
  have eq14608 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14601
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14601
    | exact resolve eq14601 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14601
  have eq14622 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14608
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14608
    | exact resolve eq14608 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14608
  have eq14625 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14622
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14622
    | exact resolve eq14622 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14622
  have eq14627 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14625
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14625
    | exact resolve eq14625 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14625
  have eq14629 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq14627
    | exact resolve eq14627 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14627
  have eq14751 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq14195 eq28
    | exact resolve eq28 eq14195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14195
  have eq14766 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14629 eq28
    | exact resolve eq28 eq14629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14629
  have eq14780 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14766
       have r₂ := eq14448
       grind)
    | exact resolve eq14766 eq14448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14448 eq14766
  have eq14783 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14780 eq31
    | exact resolve eq31 eq14780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14780
  have eq14904 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq14783
    | exact resolve eq14783 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14783
  have eq14905 : x = (M.op x y) ∨ x = y := by grind
  clear eq14904
  have eq14907 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14905 eq21
    | exact resolve eq21 eq14905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15032 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14907
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14907
    | exact resolve eq14907 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14907
  have eq15101 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15032 eq14751
    | (have r₁ := eq14751
       have r₂ := eq15032
       grind)
    | exact resolve eq14751 eq15032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14751 eq15032
  have eq15102 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq15101
  have eq15103 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq15102
  have eq15366 : y = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq15103 eq31
    | exact resolve eq31 eq15103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq15103
  have eq15508 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq15366
    | exact resolve eq15366 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq15366
  have eq15509 : y = (M.op x y) ∨ x = y := by grind
  clear eq15508
  have eq15576 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15509 eq14905
    | exact resolve eq14905 eq15509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14905 eq15509
  have eq15579 : x = y := by grind
  clear eq15576
  have eq15645 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15579
       grind)
    | exact superpose eq15579 eq19
    | exact resolve eq19 eq15579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq15646 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq15579
       grind)
    | exact superpose eq15579 eq25
    | exact resolve eq25 eq15579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15579
  have eq15768 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15646
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15646
    | exact resolve eq15646 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15646
  have eq15771 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15768 eq27
    | exact resolve eq27 eq15768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq15896 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60
       have i₂ := eq15645
       grind)
    | exact superpose eq15645 eq60
    | exact resolve eq60 eq15645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq15898 : x ≠ (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq15645
       grind)
    | exact superpose eq15645 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq15645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15645
  have eq15899 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq15896
    | exact resolve eq15896 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15896
  have eq15921 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15899 eq29
    | (have j0 := eq29 (σ x)
       grind)
    | exact resolve eq29 eq15899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq15922 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15771 eq15921
    | exact resolve eq15921 eq15771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15921
  have eq15935 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15922
       have r₂ := eq28
       grind)
    | exact resolve eq15922 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15922
  have eq15939 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15771 eq15935
    | exact resolve eq15935 eq15771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15935
  have eq15945 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15939 eq28
    | exact resolve eq28 eq15939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15946 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15939 eq53
    | (have r₁ := eq53
       have r₂ := eq15939
       grind)
    | exact resolve eq53 eq15939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq15939
  have eq15949 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15946
  have eq15953 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15768 eq15949
    | exact resolve eq15949 eq15768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15768 eq15949
  have eq16365 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15953 eq51
    | exact resolve eq51 eq15953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq16373 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15953 eq15899
    | exact resolve eq15899 eq15953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15899 eq15953
  have eq16380 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq16373
  have eq16386 : x = (M.op x y) := by
    first
    | (have r₁ := eq16380
       have r₂ := eq15945
       grind)
    | exact resolve eq16380 eq15945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15945 eq16380
  have eq16394 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq16365
    | exact resolve eq16365 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16365
  have eq16401 : x = (k x x) := by
    first
    | (have r₁ := eq16394
       have r₂ := eq15898
       grind)
    | exact resolve eq16394 eq15898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15898 eq16394
  have eq16405 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq16386 eq21
    | exact resolve eq21 eq16386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16386
  have eq16538 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16405
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16405
    | exact resolve eq16405 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16405
  have eq16764 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq491 x
       have i₂ := eq16401
       grind)
    | exact superpose eq16401 eq491
    | (have j0 := eq491 x
       grind)
    | exact resolve eq491 eq16401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq16401
  have eq16767 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq16764
  have eq16773 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16767
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16767
    | exact resolve eq16767 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq16767
  have eq16785 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15771 eq16773
    | exact resolve eq16773 eq15771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15771 eq16773
  have eq16795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16538 eq16785
    | exact resolve eq16785 eq16538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16538 eq16785
  have eq16804 : False := by grind
  exact eq16804

/-- `x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else if X = Y then m(Y,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyx_y_pyx_x_x_y_x_y_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
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
  have eq29 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X1
    grind
  have eq30 : x = (τ (σ x)) := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  clear eq37
  have eq51 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : x ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq29 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq29
    | (have j0 := eq29 (σ X0)
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq29 x
       grind)
    | exact superpose eq29 eq45
    | (have j1 := eq29 x
       grind)
    | exact resolve eq45 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq68 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq94
    | exact resolve eq94 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq491 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq58 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq681 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq83 X1 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq14 (σ X0) (σ X0)
       have r₂ := eq83 X0 X0
       grind)
    | (have r₁ := eq14 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq14 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq685 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq682 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq682 X0 X0
       have r₂ := eq14 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq682 X0 X1
       have r₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq682 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq686 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq681 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq681 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq681 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | exact resolve eq681 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq695 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq685 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq685
    | (have j0 := eq685 X0 X1
       grind)
    | exact resolve eq685 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq696 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq686 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq686
    | (have j0 := eq686 X0 X1
       grind)
    | exact resolve eq686 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq697 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq696 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq13933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq13934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq13933
    | exact resolve eq13933 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13933
  have eq13945 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq13934
       have r₂ := eq28
       grind)
    | exact resolve eq13934 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13934
  have eq13947 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq13945
    | exact resolve eq13945 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13945
  have eq13949 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq13947
    | exact resolve eq13947 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13947
  have eq13951 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13949 eq69
    | (have r₁ := eq69
       have r₂ := eq13949
       grind)
    | exact resolve eq69 eq13949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq13949
  have eq13955 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13951
  have eq13956 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13955
  have eq13962 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13956 eq82
    | exact resolve eq82 eq13956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13956
  have eq13989 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq13962
    | exact resolve eq13962 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13962
  have eq13995 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq13989
       have r₂ := eq68
       grind)
    | exact resolve eq13989 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13989
  have eq14010 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq13995
       grind)
    | exact superpose eq13995 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq13995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13995
  have eq14011 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14010
  have eq14016 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14011
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14011
    | exact resolve eq14011 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14011
  have eq14017 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14016
  have eq14031 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14017
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14017
    | exact resolve eq14017 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14017
  have eq14048 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14031 eq53
    | (have r₁ := eq53
       have r₂ := eq14031
       grind)
    | exact resolve eq53 eq14031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14031
  have eq14050 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14048
  have eq14109 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14050 eq82
    | exact resolve eq82 eq14050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq14050
  have eq14141 : y = (k y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq14109
    | exact resolve eq14109 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14109
  have eq14146 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14141
       have r₂ := eq52
       grind)
    | exact resolve eq14141 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq14141
  have eq14162 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq697 y x
       have i₂ := eq14146
       grind)
    | exact superpose eq14146 eq697
    | (have j0 := eq697 x y
       grind)
    | exact resolve eq697 eq14146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq14163 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq14146
       grind)
    | exact superpose eq14146 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq14146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14146
  have eq14164 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14163
  have eq14165 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14162
  have eq14166 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14165
  have eq14171 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14164
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14164
    | exact resolve eq14164 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14164
  have eq14172 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq14171
  have eq14173 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14166
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14166
    | exact resolve eq14166 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14166
  have eq14186 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14172
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14172
    | exact resolve eq14172 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14172
  have eq14187 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14173
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14173
    | exact resolve eq14173 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14173
  have eq14188 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq14187
  have eq14191 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14188
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14188
    | exact resolve eq14188 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14188
  have eq14193 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14191
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14191
    | exact resolve eq14191 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14191
  have eq14195 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14193
    | exact resolve eq14193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14193
  have eq14202 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14186 eq31
    | exact resolve eq31 eq14186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14186
  have eq14318 : x = y ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq14202
    | exact resolve eq14202 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14202
  have eq14319 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq14318
  have eq14321 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14319 eq21
    | exact resolve eq21 eq14319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14325 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14319 eq68
    | (have r₁ := eq68
       have r₂ := eq14319
       grind)
    | exact resolve eq68 eq14319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq14319
  have eq14386 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq14325
  have eq14387 : x = (k y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq14386
  have eq14448 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14321
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14321
    | exact resolve eq14321 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14321
  have eq14597 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq695 y x
       have i₂ := eq14387
       grind)
    | exact superpose eq14387 eq695
    | (have j0 := eq695 y x
       grind)
    | exact resolve eq695 eq14387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq14387
  have eq14600 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq14597
  have eq14601 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq14600
  have eq14608 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14601
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14601
    | exact resolve eq14601 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14601
  have eq14622 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14608
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14608
    | exact resolve eq14608 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14608
  have eq14625 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14622
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14622
    | exact resolve eq14622 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14622
  have eq14627 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14625
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14625
    | exact resolve eq14625 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14625
  have eq14629 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq14627
    | exact resolve eq14627 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14627
  have eq14751 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq14195 eq28
    | exact resolve eq28 eq14195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14195
  have eq14766 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14629 eq28
    | exact resolve eq28 eq14629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14629
  have eq14780 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14766
       have r₂ := eq14448
       grind)
    | exact resolve eq14766 eq14448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14448 eq14766
  have eq14783 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14780 eq31
    | exact resolve eq31 eq14780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14780
  have eq14904 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq14783
    | exact resolve eq14783 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14783
  have eq14905 : x = (M.op x y) ∨ x = y := by grind
  clear eq14904
  have eq14907 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14905 eq21
    | exact resolve eq21 eq14905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15032 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14907
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14907
    | exact resolve eq14907 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14907
  have eq15101 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15032 eq14751
    | (have r₁ := eq14751
       have r₂ := eq15032
       grind)
    | exact resolve eq14751 eq15032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14751 eq15032
  have eq15102 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq15101
  have eq15103 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq15102
  have eq15366 : y = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq15103 eq31
    | exact resolve eq31 eq15103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq15103
  have eq15508 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq15366
    | exact resolve eq15366 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq15366
  have eq15509 : y = (M.op x y) ∨ x = y := by grind
  clear eq15508
  have eq15576 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15509 eq14905
    | exact resolve eq14905 eq15509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14905 eq15509
  have eq15579 : x = y := by grind
  clear eq15576
  have eq15645 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15579
       grind)
    | exact superpose eq15579 eq19
    | exact resolve eq19 eq15579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq15646 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq15579
       grind)
    | exact superpose eq15579 eq25
    | exact resolve eq25 eq15579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15579
  have eq15768 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15646
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15646
    | exact resolve eq15646 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15646
  have eq15771 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15768 eq27
    | exact resolve eq27 eq15768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq15896 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60
       have i₂ := eq15645
       grind)
    | exact superpose eq15645 eq60
    | exact resolve eq60 eq15645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq15898 : x ≠ (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq15645
       grind)
    | exact superpose eq15645 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq15645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15645
  have eq15899 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq15896
    | exact resolve eq15896 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15896
  have eq15921 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15899 eq29
    | (have j0 := eq29 (σ x)
       grind)
    | exact resolve eq29 eq15899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq15922 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15771 eq15921
    | exact resolve eq15921 eq15771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15921
  have eq15935 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15922
       have r₂ := eq28
       grind)
    | exact resolve eq15922 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15922
  have eq15939 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15771 eq15935
    | exact resolve eq15935 eq15771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15935
  have eq15945 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15939 eq28
    | exact resolve eq28 eq15939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15946 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15939 eq53
    | (have r₁ := eq53
       have r₂ := eq15939
       grind)
    | exact resolve eq53 eq15939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq15939
  have eq15949 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15946
  have eq15953 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15768 eq15949
    | exact resolve eq15949 eq15768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15768 eq15949
  have eq16365 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15953 eq51
    | exact resolve eq51 eq15953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq16373 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15953 eq15899
    | exact resolve eq15899 eq15953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15899 eq15953
  have eq16380 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq16373
  have eq16386 : x = (M.op x y) := by
    first
    | (have r₁ := eq16380
       have r₂ := eq15945
       grind)
    | exact resolve eq16380 eq15945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15945 eq16380
  have eq16394 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq16365
    | exact resolve eq16365 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16365
  have eq16401 : x = (k x x) := by
    first
    | (have r₁ := eq16394
       have r₂ := eq15898
       grind)
    | exact resolve eq16394 eq15898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15898 eq16394
  have eq16405 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq16386 eq21
    | exact resolve eq21 eq16386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16386
  have eq16538 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16405
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16405
    | exact resolve eq16405 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16405
  have eq16764 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq491 x
       have i₂ := eq16401
       grind)
    | exact superpose eq16401 eq491
    | (have j0 := eq491 x
       grind)
    | exact resolve eq491 eq16401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq16401
  have eq16767 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq16764
  have eq16773 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16767
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16767
    | exact resolve eq16767 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq16767
  have eq16785 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15771 eq16773
    | exact resolve eq16773 eq15771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15771 eq16773
  have eq16795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16538 eq16785
    | exact resolve eq16785 eq16538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16538 eq16785
  have eq16804 : False := by grind
  exact eq16804

/-- `x □ y = if m(Y,X) = Y then Y else if m(Y,X) = X then X else if X = Y then m(X,X)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyx_y_pyx_x_x_y_y_x_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
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
  have eq29 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X1
    grind
  have eq30 : x = (τ (σ x)) := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq39 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  clear eq37
  have eq51 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : x ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq29 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq29
    | (have j0 := eq29 (σ X0)
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq29 x
       grind)
    | exact superpose eq29 eq45
    | (have j1 := eq29 x
       grind)
    | exact resolve eq45 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq68 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq94
    | exact resolve eq94 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq122 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq39
    | (have j0 := eq39 x
       grind)
    | exact resolve eq39 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq133 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq122 eq16
    | exact resolve eq16 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq491 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq58 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq683 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq5868 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq684 x y
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq684
    | (have j0 := eq684 x y
       grind)
    | exact resolve eq684 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq5899 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5868
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5868
    | exact resolve eq5868 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5868
  have eq5983 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5899
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5899
    | exact resolve eq5899 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5899
  have eq6067 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5983
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5983
    | exact resolve eq5983 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5983
  have eq6151 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq6067
    | exact resolve eq6067 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6067
  have eq6234 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6151
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6151
    | exact resolve eq6151 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6151
  have eq6316 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6234
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6234
    | exact resolve eq6234 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6234
  have eq6398 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq6316
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6316
    | exact resolve eq6316 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6316
  have eq6465 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq6398
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6398
    | exact resolve eq6398 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6398
  have eq6473 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq6465
    | exact resolve eq6465 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6465
  have eq12452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12453 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq12452
    | exact resolve eq12452 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12452
  have eq12464 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq12453
       have r₂ := eq28
       grind)
    | exact resolve eq12453 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12453
  have eq12466 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq12464
    | exact resolve eq12464 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12464
  have eq12468 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq12466
    | exact resolve eq12466 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12466
  have eq12470 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12468 eq69
    | (have r₁ := eq69
       have r₂ := eq12468
       grind)
    | exact resolve eq69 eq12468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq12472 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12468 eq28
    | exact resolve eq28 eq12468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12468
  have eq12474 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12470
  have eq12475 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12474
  have eq12481 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12475 eq82
    | exact resolve eq82 eq12475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12482 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12475 eq97
    | exact resolve eq97 eq12475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12475
  have eq12494 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12482
  have eq12504 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12494
       have r₂ := eq12472
       grind)
    | exact resolve eq12494 eq12472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12472 eq12494
  have eq12505 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq12481
    | exact resolve eq12481 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12481
  have eq12510 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq12505
       have r₂ := eq68
       grind)
    | exact resolve eq12505 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12505
  have eq12512 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12504 eq53
    | (have r₁ := eq53
       have r₂ := eq12504
       grind)
    | exact resolve eq53 eq12504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12513 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12504 eq28
    | exact resolve eq28 eq12504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12504
  have eq12514 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq12512
  have eq12528 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq683 x y
       have i₂ := eq12510
       grind)
    | exact superpose eq12510 eq683
    | (have j0 := eq683 x y
       grind)
    | exact resolve eq683 eq12510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq12510
  have eq12531 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12528
  have eq12534 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12531
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12531
    | exact resolve eq12531 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12531
  have eq12545 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12534
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12534
    | exact resolve eq12534 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12534
  have eq12546 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq12545
    | exact resolve eq12545 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12545
  have eq12547 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12546
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12546
    | exact resolve eq12546 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12546
  have eq12548 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12547
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12547
    | exact resolve eq12547 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12547
  have eq12549 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12548
  have eq12550 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12549
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12549
    | exact resolve eq12549 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12549
  have eq12551 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12550
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12550
    | exact resolve eq12550 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12550
  have eq12552 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq12551
    | exact resolve eq12551 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12551
  have eq12553 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12552
  have eq12557 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12553 eq28
    | exact resolve eq28 eq12553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12553
  have eq12569 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12514 eq97
    | exact resolve eq97 eq12514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq12514
  have eq12583 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12569
  have eq12594 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12583
       have r₂ := eq12513
       grind)
    | exact resolve eq12583 eq12513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12513 eq12583
  have eq12602 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq12594 eq31
    | exact resolve eq31 eq12594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12594
  have eq12719 : x = y ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq12602
    | exact resolve eq12602 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12602
  have eq12720 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12719
  have eq12722 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12720 eq21
    | exact resolve eq21 eq12720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12726 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12720 eq68
    | (have r₁ := eq68
       have r₂ := eq12720
       grind)
    | exact resolve eq68 eq12720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq12720
  have eq12787 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq12726
  have eq12788 : y = (k y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq12787
  have eq12849 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12722
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12722
    | exact resolve eq12722 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12722
  have eq12860 : (k y x) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12849 eq82
    | exact resolve eq82 eq12849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq12916 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12849 eq12557
    | (have r₁ := eq12557
       have r₂ := eq12849
       grind)
    | exact resolve eq12557 eq12849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12557
  have eq12919 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12916
  have eq12920 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq12919
  have eq12974 : (k y x) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq133 eq12860
    | exact resolve eq12860 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12860
  have eq12984 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq12788
       grind)
    | exact superpose eq12788 eq75
    | exact resolve eq75 eq12788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12788
  have eq13009 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12984
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12984
    | exact resolve eq12984 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12984
  have eq13021 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12849 eq13009
    | exact resolve eq13009 eq12849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12849 eq13009
  have eq13048 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq13021
  have eq13065 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq13048 eq133
    | exact resolve eq133 eq13048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq13048
  have eq13084 : (M.op x y) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq13065
    | exact resolve eq13065 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13065
  have eq13124 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12920 eq53
    | (have r₁ := eq53
       have r₂ := eq12920
       grind)
    | exact resolve eq53 eq12920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12920
  have eq13125 : (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq13124
  have eq13607 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12974 eq13084
    | exact resolve eq13084 eq12974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12974 eq13084
  have eq13614 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq13607
  have eq13646 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq13614
       grind)
    | exact superpose eq13614 eq75
    | exact resolve eq75 eq13614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13614
  have eq13676 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq13646
    | exact resolve eq13646 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13646
  have eq15533 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13125 eq13676
    | exact resolve eq13676 eq13125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13125 eq13676
  have eq15541 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq15533
  have eq15568 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq15541 eq30
    | exact resolve eq30 eq15541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15541
  have eq15712 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq15568
    | exact resolve eq15568 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15568
  have eq15713 : x = (M.op x y) ∨ x = y := by grind
  clear eq15712
  have eq15715 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq15713 eq21
    | exact resolve eq21 eq15713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15717 : x ≠ x ∨ x = (k y x) ∨ x = y := by
    first
    | exact superpose eq15713 eq52
    | (have r₁ := eq52
       have r₂ := eq15713
       grind)
    | exact resolve eq52 eq15713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq15778 : x = (k y x) ∨ x = y := by grind
  clear eq15717
  have eq15840 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq15715
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15715
    | exact resolve eq15715 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15715
  have eq16054 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq15840 eq27
    | exact resolve eq27 eq15840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16205 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq15778
       grind)
    | exact superpose eq15778 eq75
    | exact resolve eq75 eq15778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq15778
  have eq16239 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq16205
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16205
    | exact resolve eq16205 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16205
  have eq16250 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq16054 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq16054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16054
  have eq16254 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq16250
       have r₂ := eq28
       grind)
    | exact resolve eq16250 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16250
  have eq16472 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15840 eq16239
    | exact resolve eq16239 eq15840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16239
  have eq16515 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq16472
  have eq18455 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq15840 eq6473
    | exact resolve eq6473 eq15840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6473 eq15840
  have eq18481 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq18455
       have r₂ := eq16515
       grind)
    | exact resolve eq18455 eq16515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18455
  have eq18482 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq18481
       have r₂ := eq28
       grind)
    | exact resolve eq18481 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18481
  have eq20608 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq18482 eq16254
    | (have r₁ := eq16254
       have r₂ := eq18482
       grind)
    | exact resolve eq16254 eq18482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16254 eq18482
  have eq20619 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20608
  have eq20620 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20619
  have eq20637 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20620 eq16515
    | exact resolve eq16515 eq20620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16515 eq20620
  have eq20647 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq20637
  have eq20918 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20647 eq31
    | exact resolve eq31 eq20647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq20647
  have eq21080 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq20918
    | exact resolve eq20918 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq20918
  have eq21149 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq21080 eq15713
    | exact resolve eq15713 eq21080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15713 eq21080
  have eq21172 : x = y := by grind
  clear eq21149
  have eq21486 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq21172
       grind)
    | exact superpose eq21172 eq19
    | exact resolve eq19 eq21172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq21487 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq21172
       grind)
    | exact superpose eq21172 eq25
    | exact resolve eq25 eq21172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq21172
  have eq21611 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq21487
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21487
    | exact resolve eq21487 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21487
  have eq21614 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21611 eq27
    | exact resolve eq27 eq21611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq21766 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60
       have i₂ := eq21486
       grind)
    | exact superpose eq21486 eq60
    | exact resolve eq60 eq21486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq21768 : x ≠ (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq21486
       grind)
    | exact superpose eq21486 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq21486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21486
  have eq21769 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq21766
    | exact resolve eq21766 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21766
  have eq22217 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21769 eq29
    | (have j0 := eq29 (σ x)
       grind)
    | exact resolve eq29 eq21769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq22219 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21614 eq22217
    | exact resolve eq22217 eq21614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22217
  have eq22233 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22219
       have r₂ := eq28
       grind)
    | exact resolve eq22219 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22219
  have eq22238 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21614 eq22233
    | exact resolve eq22233 eq21614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22233
  have eq22246 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22238 eq28
    | exact resolve eq28 eq22238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22247 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22238 eq53
    | (have r₁ := eq53
       have r₂ := eq22238
       grind)
    | exact resolve eq53 eq22238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq22238
  have eq22253 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq22247
  have eq22256 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21611 eq22253
    | exact resolve eq22253 eq21611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21611 eq22253
  have eq22715 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22256 eq51
    | exact resolve eq51 eq22256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq22726 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22256 eq21769
    | exact resolve eq21769 eq22256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21769 eq22256
  have eq22735 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq22726
  have eq22743 : x = (M.op x y) := by
    first
    | (have r₁ := eq22735
       have r₂ := eq22246
       grind)
    | exact resolve eq22735 eq22246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22246 eq22735
  have eq22751 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq22715
    | exact resolve eq22715 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq22715
  have eq22759 : x = (k x x) := by
    first
    | (have r₁ := eq22751
       have r₂ := eq21768
       grind)
    | exact resolve eq22751 eq21768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21768 eq22751
  have eq22765 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq22743 eq21
    | exact resolve eq21 eq22743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22743
  have eq22905 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22765
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22765
    | exact resolve eq22765 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22765
  have eq23154 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq491 x
       have i₂ := eq22759
       grind)
    | exact superpose eq22759 eq491
    | (have j0 := eq491 x
       grind)
    | exact resolve eq491 eq22759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq22759
  have eq23157 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq23154
  have eq23163 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq23157
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23157
    | exact resolve eq23157 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq23157
  have eq23176 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21614 eq23163
    | exact resolve eq23163 eq21614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21614 eq23163
  have eq23187 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22905 eq23176
    | exact resolve eq23176 eq22905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22905 eq23176
  have eq23197 : False := by grind
  exact eq23197
