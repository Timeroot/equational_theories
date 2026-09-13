import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then m(Y,X) else if m(X,Y) = X then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_pxx_x_pxy_x_pyx_pyx_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq67 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq68 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq16
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (k x y) := by
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
  have eq85 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq91 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq95 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq98 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq67
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq67 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq98
  have eq110 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq95
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq156 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq125
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq125
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq156
  have eq523 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq3001 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq90 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq90
    | (have j0 := eq90 x
       grind)
    | exact resolve eq90 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq3007 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3001
  have eq3011 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3007
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3007
    | exact resolve eq3007 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3007
  have eq3028 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | (have r₁ := eq3011
       have r₂ := eq14 x (σ x)
       grind)
    | exact resolve eq3011 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011
  have eq3034 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3028 eq49
    | exact resolve eq49 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq3156 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq91 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq91
    | (have j0 := eq91 y
       grind)
    | exact resolve eq91 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq3161 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3156
  have eq3164 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3161
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq3161
    | exact resolve eq3161 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3161
  have eq3188 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | (have r₁ := eq3164
       have r₂ := eq14 x (σ y)
       grind)
    | exact resolve eq3164 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3164
  have eq3210 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3188 eq78
    | exact resolve eq78 eq3188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3339 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq126
    | (have j0 := eq126 (M.op x y)
       grind)
    | exact resolve eq126 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq3343 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3339
  have eq3345 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq125 eq3343
    | exact resolve eq3343 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq3343
  have eq3376 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq14 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq3345
       have r₂ := eq14 x (σ (M.op x y))
       grind)
    | exact resolve eq3345 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3345
  have eq3415 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3376 eq159
    | exact resolve eq159 eq3376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq8259 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3188 eq109
    | exact resolve eq109 eq3188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq8260 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3028 eq110
    | exact resolve eq110 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq8783 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3376 eq164
    | exact resolve eq164 eq3376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq3376
  have eq11132 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq8259
       grind)
    | exact superpose eq8259 eq16
    | exact resolve eq16 eq8259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8259
  have eq11181 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3210 eq11132
    | exact resolve eq11132 eq3210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11132
  have eq11184 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq14 y y
       grind)
    | (have r₁ := eq11181
       have r₂ := eq14 x y
       grind)
    | exact resolve eq11181 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11181
  have eq11185 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq11184
       grind)
    | exact superpose eq11184 eq67
    | exact resolve eq67 eq11184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq11210 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq3188 eq11185
    | exact resolve eq11185 eq3188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3188 eq11185
  have eq11217 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq8260
       grind)
    | exact superpose eq8260 eq16
    | exact resolve eq16 eq8260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8260
  have eq11268 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3034 eq11217
    | exact resolve eq11217 eq3034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11217
  have eq11271 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq14 x x
       grind)
    | (have r₁ := eq11268
       have r₂ := eq14 x x
       grind)
    | exact resolve eq11268 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11268
  have eq11272 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11271
       grind)
    | exact superpose eq11271 eq43
    | exact resolve eq43 eq11271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq11297 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq3028 eq11272
    | exact resolve eq11272 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3028 eq11272
  have eq11858 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8783 eq16
    | exact resolve eq16 eq8783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8783
  have eq11913 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3415 eq11858
    | exact resolve eq11858 eq3415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11858
  have eq11916 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq14 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq11913
       have r₂ := eq14 x (M.op x y)
       grind)
    | exact resolve eq11913 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11913
  have eq18428 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq18428
    | exact resolve eq18428 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18428
  have eq18440 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq18429
       have r₂ := eq27
       grind)
    | exact resolve eq18429 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18429
  have eq18444 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq18440
    | exact resolve eq18440 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18440
  have eq18446 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq18444 eq3210
    | exact resolve eq3210 eq18444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18444
  have eq18467 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18446
       have i₂ := eq11184
       grind)
    | exact superpose eq11184 eq18446
    | exact resolve eq18446 eq11184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18446
  have eq18476 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq18467
    | exact resolve eq18467 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18467
  have eq18477 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq18476
  have eq18479 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq18477 eq3034
    | exact resolve eq3034 eq18477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18477
  have eq18500 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18479
       have i₂ := eq11271
       grind)
    | exact superpose eq11271 eq18479
    | exact resolve eq18479 eq11271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18479
  have eq18509 : x = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq18500
    | exact resolve eq18500 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18500
  have eq18510 : y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18509
  have eq18518 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11210
       have i₂ := eq18510
       grind)
    | exact superpose eq18510 eq11210
    | exact resolve eq11210 eq18510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18521 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59 y X0
       have i₂ := eq18510
       grind)
    | exact superpose eq18510 eq59
    | (have j0 := eq59 y X0
       grind)
    | (have r₁ := eq59 y x
       have r₂ := eq18510
       grind)
    | (have r₁ := eq59 x x
       have r₂ := eq18510
       grind)
    | exact resolve eq59 eq18510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18510
  have eq18524 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18521 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18521
  have eq18527 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18518
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18518
    | exact resolve eq18518 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18518
  have eq18822 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18527 eq59
    | (have j0 := eq59 (σ y) X0
       grind)
    | (have r₁ := eq59 (σ y) x
       have r₂ := eq18527
       grind)
    | (have r₁ := eq59 x x
       have r₂ := eq18527
       grind)
    | exact resolve eq59 eq18527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18527
  have eq18825 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18822 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18822
  have eq19000 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq18524 x
       grind)
    | exact superpose eq18524 eq66
    | exact resolve eq66 eq18524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18524
  have eq19040 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19000
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19000
    | exact resolve eq19000 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19000
  have eq19065 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq19040
    | exact resolve eq19040 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19040
  have eq19843 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18825 eq19065
    | exact resolve eq19065 eq18825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18825 eq19065
  have eq19847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19843
  have eq19850 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19847
    | exact resolve eq19847 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19847
  have eq19876 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19850
       have r₂ := eq27
       grind)
    | exact resolve eq19850 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19850
  have eq19884 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11297
       have i₂ := eq19876
       grind)
    | exact superpose eq19876 eq11297
    | exact resolve eq11297 eq19876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19888 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq19876
       grind)
    | exact superpose eq19876 eq14
    | (have j0 := eq14 X0 x
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq19876
       grind)
    | exact resolve eq14 eq19876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19876
  have eq19889 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19888 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19888
  have eq19893 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19884
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19884
    | exact resolve eq19884 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19884
  have eq20191 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19893 eq14
    | (have j0 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq19893
       grind)
    | exact resolve eq14 eq19893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19893
  have eq20192 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20191 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20191
  have eq20239 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq19889 y
       grind)
    | exact superpose eq19889 eq66
    | exact resolve eq66 eq19889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19889
  have eq20317 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20239
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20239
    | exact resolve eq20239 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20239
  have eq20340 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq20317
    | exact resolve eq20317 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20317
  have eq20849 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20192 eq20340
    | exact resolve eq20340 eq20192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20192 eq20340
  have eq20883 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20849
  have eq20898 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq20883
    | exact resolve eq20883 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20883
  have eq20912 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20898
       have r₂ := eq27
       grind)
    | exact resolve eq20898 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20898
  have eq21197 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20912 eq85
    | (have r₁ := eq85
       have r₂ := eq20912
       grind)
    | exact resolve eq85 eq20912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq21198 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20912 eq27
    | exact resolve eq27 eq20912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20912
  have eq21199 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21197
  have eq34235 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21199 eq3210
    | exact resolve eq3210 eq21199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21199
  have eq34256 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq34235
       have i₂ := eq11184
       grind)
    | exact superpose eq11184 eq34235
    | exact resolve eq34235 eq11184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34235
  have eq34265 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq34256
    | exact resolve eq34256 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34256
  have eq34273 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34265 eq115
    | exact resolve eq115 eq34265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq34265
  have eq34286 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq34273
  have eq34297 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq34286
       have r₂ := eq21198
       grind)
    | exact resolve eq34286 eq21198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21198 eq34286
  have eq34305 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34297 eq3034
    | exact resolve eq3034 eq34297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3034 eq34297
  have eq34326 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq34305
       have i₂ := eq11271
       grind)
    | exact superpose eq11271 eq34305
    | exact resolve eq34305 eq11271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11271 eq34305
  have eq34335 : x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq34326
    | exact resolve eq34326 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq34326
  have eq34336 : y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq34335
  have eq34629 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11210
       have i₂ := eq34336
       grind)
    | exact superpose eq34336 eq11210
    | exact resolve eq11210 eq34336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34632 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59 y X0
       have i₂ := eq34336
       grind)
    | exact superpose eq34336 eq59
    | (have j0 := eq59 y X0
       grind)
    | (have r₁ := eq59 y x
       have r₂ := eq34336
       grind)
    | (have r₁ := eq59 x x
       have r₂ := eq34336
       grind)
    | exact resolve eq59 eq34336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34336
  have eq34635 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq34632 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34632
  have eq34638 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq34629
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34629
    | exact resolve eq34629 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34629
  have eq34656 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34638 eq59
    | (have j0 := eq59 (σ y) X0
       grind)
    | (have r₁ := eq59 (σ y) x
       have r₂ := eq34638
       grind)
    | (have r₁ := eq59 x x
       have r₂ := eq34638
       grind)
    | exact resolve eq59 eq34638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34638
  have eq34659 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq34656 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34656
  have eq35244 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq34635 x
       grind)
    | exact superpose eq34635 eq66
    | exact resolve eq66 eq34635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34635
  have eq35290 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35244
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35244
    | exact resolve eq35244 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35244
  have eq35333 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq35290
    | exact resolve eq35290 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35290
  have eq35916 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34659 eq35333
    | exact resolve eq35333 eq34659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34659 eq35333
  have eq35920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq35916
  have eq35927 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq35920
    | exact resolve eq35920 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35920
  have eq35953 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq35927
       have r₂ := eq27
       grind)
    | exact resolve eq35927 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35927
  have eq35961 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11297
       have i₂ := eq35953
       grind)
    | exact superpose eq35953 eq11297
    | exact resolve eq11297 eq35953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35965 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq35953
       grind)
    | exact superpose eq35953 eq14
    | (have j0 := eq14 X0 x
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq35953
       grind)
    | exact resolve eq14 eq35953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35953
  have eq35966 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq35965 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35965
  have eq35970 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35961
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35961
    | exact resolve eq35961 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35961
  have eq36278 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq35970 eq14
    | (have j0 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq35970
       grind)
    | exact resolve eq14 eq35970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35970
  have eq36279 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq36278 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36278
  have eq36344 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66
       have i₂ := eq35966 y
       grind)
    | exact superpose eq35966 eq66
    | exact resolve eq66 eq35966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35966
  have eq36492 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36344
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq36344
    | exact resolve eq36344 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36344
  have eq36515 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq36492
    | exact resolve eq36492 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36492
  have eq37400 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36279 eq36515
    | exact resolve eq36515 eq36279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36279 eq36515
  have eq37465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq37400
  have eq37484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq37465
    | exact resolve eq37465 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37465
  have eq37498 : x = (M.op x y) := by
    first
    | (have r₁ := eq37484
       have r₂ := eq27
       grind)
    | exact resolve eq37484 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37484
  have eq37500 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq37498 eq20
    | exact resolve eq20 eq37498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37507 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq37498 eq84
    | (have r₁ := eq84
       have r₂ := eq37498
       grind)
    | exact resolve eq84 eq37498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq37606 : y = (M.op y y) ∨ x = (M.op x x) ∨ x = (k x y) := by grind
  clear eq37507
  have eq37710 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37500
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37500
    | exact resolve eq37500 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37500
  have eq38132 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq37710 eq26
    | exact resolve eq26 eq37710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43891 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11210
       have i₂ := eq37606
       grind)
    | exact superpose eq37606 eq11210
    | exact resolve eq11210 eq37606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43894 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq59 y X0
       have i₂ := eq37606
       grind)
    | exact superpose eq37606 eq59
    | (have j0 := eq59 y X0
       grind)
    | (have r₁ := eq59 y x
       have r₂ := eq37606
       grind)
    | (have r₁ := eq59 x x
       have r₂ := eq37606
       grind)
    | exact resolve eq59 eq37606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37606
  have eq43897 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq43894 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43894
  have eq43900 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq43891
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43891
    | exact resolve eq43891 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43891
  have eq44405 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq43900 eq59
    | (have j0 := eq59 (σ y) X0
       grind)
    | (have r₁ := eq59 (σ y) x
       have r₂ := eq43900
       grind)
    | (have r₁ := eq59 x x
       have r₂ := eq43900
       grind)
    | exact resolve eq59 eq43900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43900
  have eq44408 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq44405 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44405
  have eq52746 : (k (σ y) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) ∨ x = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq43897 sF0
       grind)
    | exact superpose eq43897 eq68
    | exact resolve eq68 eq43897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43897
  have eq52767 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq37498 eq52746
    | exact resolve eq52746 eq37498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52746
  have eq52874 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq52767
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52767
    | exact resolve eq52767 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52767
  have eq52932 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq52874
    | exact resolve eq52874 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52874
  have eq55587 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) ∨ x = (k x y) ∨ x = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq44408 eq52932
    | exact resolve eq52932 eq44408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44408 eq52932
  have eq55606 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) ∨ x = (k x y) := by grind
  clear eq55587
  have eq55620 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq38132 eq55606
    | exact resolve eq55606 eq38132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55606
  have eq55685 : x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq55620
       have r₂ := eq27
       grind)
    | exact resolve eq55620 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55620
  have eq55738 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq523 x y
       have i₂ := eq55685
       grind)
    | exact superpose eq55685 eq523
    | (have j0 := eq523 x x
       grind)
    | exact resolve eq523 eq55685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523 eq55685
  have eq55741 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq55738
  have eq55749 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq55741
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq55741
    | exact resolve eq55741 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55741
  have eq55764 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq37710 eq55749
    | exact resolve eq55749 eq37710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55749
  have eq55778 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq55764
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq55764
    | exact resolve eq55764 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55764
  have eq55787 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq55778
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq55778
    | exact resolve eq55778 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55778
  have eq55791 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq55787
    | exact resolve eq55787 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq55787
  have eq55792 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq37710 eq55791
    | exact resolve eq55791 eq37710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55791
  have eq55793 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq55792
       have r₂ := eq27
       grind)
    | exact resolve eq55792 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55792
  have eq55794 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq55793
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq55793
    | exact resolve eq55793 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55793
  have eq57689 : (τ (σ y)) = (k y y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq55794 eq3210
    | exact resolve eq3210 eq55794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3210 eq55794
  have eq57710 : (τ (σ y)) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq57689
       have i₂ := eq11184
       grind)
    | exact superpose eq11184 eq57689
    | exact resolve eq57689 eq11184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11184 eq57689
  have eq57719 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq57710
    | exact resolve eq57710 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq57710
  have eq57725 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq57719 eq3415
    | exact resolve eq3415 eq57719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3415 eq57719
  have eq57746 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq11916 eq57725
    | exact resolve eq57725 eq11916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11916 eq57725
  have eq57755 : (τ (σ (M.op x y))) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq37498 eq57746
    | exact resolve eq57746 eq37498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57746
  have eq57764 : (M.op x y) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq57755
    | exact resolve eq57755 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq57755
  have eq57773 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq37498 eq57764
    | exact resolve eq57764 eq37498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57764
  have eq57774 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq57773
  have eq57785 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11210
       have i₂ := eq57774
       grind)
    | exact superpose eq57774 eq11210
    | exact resolve eq11210 eq57774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11210
  have eq57792 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq59 y X0
       have i₂ := eq57774
       grind)
    | exact superpose eq57774 eq59
    | (have j0 := eq59 y X0
       grind)
    | (have r₁ := eq59 y x
       have r₂ := eq57774
       grind)
    | (have r₁ := eq59 x x
       have r₂ := eq57774
       grind)
    | exact resolve eq59 eq57774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57774
  have eq57795 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq57792 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57792
  have eq57802 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq57785
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq57785
    | exact resolve eq57785 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq57785
  have eq57827 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq57802 eq59
    | (have j0 := eq59 (σ y) X0
       grind)
    | (have r₁ := eq59 (σ y) x
       have r₂ := eq57802
       grind)
    | (have r₁ := eq59 x x
       have r₂ := eq57802
       grind)
    | exact resolve eq59 eq57802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq57802
  have eq57830 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq57827 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57827
  have eq58346 : (k (σ y) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq68
       have i₂ := eq57795 sF0
       grind)
    | exact superpose eq57795 eq68
    | exact resolve eq68 eq57795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq57795
  have eq58371 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq37498 eq58346
    | exact resolve eq58346 eq37498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37498 eq58346
  have eq58478 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq58371
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58371
    | exact resolve eq58371 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58371
  have eq58536 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq58478
    | exact resolve eq58478 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58478
  have eq60215 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq57830 eq58536
    | exact resolve eq58536 eq57830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57830 eq58536
  have eq60234 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq60215
  have eq60252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38132 eq60234
    | exact resolve eq60234 eq38132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60234
  have eq60318 : x = (M.op x x) := by
    first
    | (have r₁ := eq60252
       have r₂ := eq27
       grind)
    | exact resolve eq60252 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60252
  have eq60355 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11297
       have i₂ := eq60318
       grind)
    | exact superpose eq60318 eq11297
    | exact resolve eq11297 eq60318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11297
  have eq60363 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq60318
       grind)
    | exact superpose eq60318 eq14
    | (have j0 := eq14 X0 x
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq60318
       grind)
    | exact resolve eq14 eq60318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60318
  have eq60364 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq60363 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60363
  have eq60372 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq37710 eq60355
    | exact resolve eq60355 eq37710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60355
  have eq60385 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq60372
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq60372
    | exact resolve eq60372 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq60372
  have eq60394 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq37710 eq60385
    | exact resolve eq60385 eq37710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60385
  have eq60415 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq60394 eq14
    | (have j0 := eq14 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq14 X0 (σ (M.op x y))
       have r₂ := eq60394
       grind)
    | exact resolve eq14 eq60394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60394
  have eq60416 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq60415 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60415
  have eq62153 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq60364 y
       grind)
    | exact superpose eq60364 eq66
    | exact resolve eq66 eq60364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq60364
  have eq62343 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq37710 eq62153
    | exact resolve eq62153 eq37710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37710 eq62153
  have eq62472 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq62343
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq62343
    | exact resolve eq62343 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq62343
  have eq62554 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq62472
    | exact resolve eq62472 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq62472
  have eq63404 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq60416 eq62554
    | exact resolve eq62554 eq60416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60416 eq62554
  have eq63542 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38132 eq63404
    | exact resolve eq63404 eq38132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38132 eq63404
  have eq63628 : False := by grind
  exact eq63628

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then m(Y,X) else if m(X,Y) = Y then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_pxx_x_pxy_y_pyx_pyx_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X0
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq298 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq382 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq298
    | exact resolve eq298 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq1104 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ y = (k x y) := by
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
  have eq1105 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1106 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq1107 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1111 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq14
    | (have j0 := eq14 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1114 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1115 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1116 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1119 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1111 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1120 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1121 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1119 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq1119 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq1119 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1122 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1120 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq1120 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq1120 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1126 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1116 (τ X0)
       have i₂ := eq382 X0 X0
       grind)
    | exact superpose eq382 eq1116
    | (have j0 := eq1116 (τ X0)
       grind)
    | exact resolve eq1116 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq1116
  have eq1127 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1121 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1121
    | (have j0 := eq1121 (σ X0) X1
       grind)
    | exact resolve eq1121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq1129 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1122 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1122
    | (have j0 := eq1122 (σ X0) X1
       grind)
    | exact resolve eq1122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq6607 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1106
       grind)
    | exact superpose eq1106 eq41
    | exact resolve eq41 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq6608 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6607
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6607
    | exact resolve eq6607 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6607
  have eq6612 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq6608
    | exact resolve eq6608 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6608
  have eq6889 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1114 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1114
    | (have j0 := eq1114 (σ X0) (σ X0)
       grind)
    | exact resolve eq1114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq19377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6612 eq1107
    | exact resolve eq1107 eq6612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107 eq6612
  have eq19390 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq19377
       have r₂ := eq27
       grind)
    | exact resolve eq19377 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19377
  have eq19755 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19390 eq14
    | (have j0 := eq14 X0 (σ y)
       grind)
    | (have r₁ := eq14 X0 (σ y)
       have r₂ := eq19390
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq19390
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq19390
       grind)
    | exact resolve eq14 eq19390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19756 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq19755 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19755
  have eq19762 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq19756 eq19390
    | exact resolve eq19390 eq19756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19390 eq19756
  have eq19767 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq19762
  have eq19778 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq19767 eq1126
    | (have j0 := eq1126 (σ y)
       grind)
    | exact resolve eq1126 eq19767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19767
  have eq19793 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq19778
  have eq19800 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq19793
    | exact resolve eq19793 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19793
  have eq19801 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq19800
  have eq19814 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19801 eq14
    | (have j0 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq19801
       grind)
    | (have r₁ := eq14 X0 y
       have r₂ := eq19801
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq19801
       grind)
    | exact resolve eq14 eq19801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19815 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19814 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19814
  have eq19843 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19815 eq19801
    | exact resolve eq19801 eq19815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19801 eq19815
  have eq19848 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq19843
  have eq20011 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19848 eq1126
    | (have j0 := eq1126 (σ x)
       grind)
    | exact resolve eq1126 eq19848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19848
  have eq20026 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq20011
  have eq20033 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq20026
    | exact resolve eq20026 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20026
  have eq20034 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq20033
  have eq20050 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 y X0
       have i₂ := eq20034
       grind)
    | exact superpose eq20034 eq28
    | (have j0 := eq28 y X0
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq20034
       grind)
    | (have r₁ := eq28 x x
       have r₂ := eq20034
       grind)
    | exact resolve eq28 eq20034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20051 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y
       have i₂ := eq20034
       grind)
    | exact superpose eq20034 eq14
    | (have j0 := eq14 X0 y
       grind)
    | (have r₁ := eq14 X0 y
       have r₂ := eq20034
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq20034
       grind)
    | exact resolve eq14 eq20034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20052 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20051 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20051
  have eq20053 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20050 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20050
  have eq20112 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20034
       have i₂ := eq20052 y
       grind)
    | exact superpose eq20052 eq20034
    | exact resolve eq20034 eq20052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20034 eq20052
  have eq20117 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq20112
  have eq20131 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1129 y X0
       have i₂ := eq20117
       grind)
    | exact superpose eq20117 eq1129
    | (have j0 := eq1129 y X0
       grind)
    | exact resolve eq1129 eq20117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20133 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6889 y y
       have i₂ := eq20117
       grind)
    | exact superpose eq20117 eq6889
    | (have j0 := eq6889 y y
       grind)
    | exact resolve eq6889 eq20117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20117
  have eq20137 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq20133
  have eq20138 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq20137
  have eq20140 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20131 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20131
  have eq20148 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20138
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20138
    | exact resolve eq20138 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20138
  have eq20149 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20140 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20140
    | (have j0 := eq20140 X0
       grind)
    | exact resolve eq20140 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20140
  have eq20211 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20053 x
       grind)
    | exact superpose eq20053 eq18
    | (have j1 := eq20053 x
       grind)
    | exact resolve eq18 eq20053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20053
  have eq20219 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq20211
       grind)
    | exact superpose eq20211 eq40
    | exact resolve eq40 eq20211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20211
  have eq20224 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20219
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20219
    | exact resolve eq20219 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20219
  have eq20230 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq20224
    | exact resolve eq20224 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20224
  have eq20259 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20149 eq26
    | (have j1 := eq20149 (σ x)
       grind)
    | exact resolve eq26 eq20149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20149
  have eq20266 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20230 eq20259
    | exact resolve eq20259 eq20230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20230 eq20259
  have eq20268 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20266
       have r₂ := eq27
       grind)
    | exact resolve eq20266 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20266
  have eq20276 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq20268
       grind)
    | exact superpose eq20268 eq14
    | (have j0 := eq14 X0 x
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq20268
       grind)
    | exact resolve eq14 eq20268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20277 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20276 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20276
  have eq20287 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20277 y
       grind)
    | exact superpose eq20277 eq18
    | (have j1 := eq20277 y
       grind)
    | exact resolve eq18 eq20277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20288 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20268
       have i₂ := eq20277 x
       grind)
    | exact superpose eq20277 eq20268
    | exact resolve eq20268 eq20277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20277
  have eq20293 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20288
  have eq20299 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq20287
       grind)
    | exact superpose eq20287 eq40
    | exact resolve eq40 eq20287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20287
  have eq20303 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20299
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20299
    | exact resolve eq20299 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20299
  have eq20309 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq20303
    | exact resolve eq20303 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20303
  have eq20325 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1127 x X0
       have i₂ := eq20293
       grind)
    | exact superpose eq20293 eq1127
    | (have j0 := eq1127 x X0
       grind)
    | exact resolve eq1127 eq20293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20293
  have eq20338 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20325 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20325
  have eq20346 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20338 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20338
    | (have j0 := eq20338 X0
       grind)
    | exact resolve eq20338 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20338
  have eq20691 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20346 eq26
    | (have j1 := eq20346 (σ y)
       grind)
    | exact resolve eq26 eq20346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20346
  have eq20705 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20309 eq20691
    | exact resolve eq20691 eq20309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20309 eq20691
  have eq20707 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20705
       have r₂ := eq27
       grind)
    | exact resolve eq20705 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20705
  have eq20709 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20707 eq1105
    | (have r₁ := eq1105
       have r₂ := eq20707
       grind)
    | exact resolve eq1105 eq20707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq20710 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20707 eq27
    | exact resolve eq27 eq20707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20711 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq20709
  have eq20912 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20711 eq91
    | exact resolve eq91 eq20711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq20711
  have eq20925 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq20912
    | exact resolve eq20912 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20912
  have eq20940 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20925 eq14
    | (have j0 := eq14 X0 (σ y)
       grind)
    | (have r₁ := eq14 X0 (σ y)
       have r₂ := eq20925
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq20925
       grind)
    | exact resolve eq14 eq20925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20941 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20940 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20940
  have eq21002 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20941 eq20925
    | exact resolve eq20925 eq20941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20925 eq20941
  have eq21011 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq21002
  have eq21024 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21011 eq1126
    | (have j0 := eq1126 (σ y)
       grind)
    | exact resolve eq1126 eq21011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21011
  have eq21039 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq21024
  have eq21046 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq21039
    | exact resolve eq21039 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21039
  have eq21060 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21046 eq14
    | (have j0 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq21046
       grind)
    | (have r₁ := eq14 X0 y
       have r₂ := eq21046
       grind)
    | exact resolve eq14 eq21046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21061 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21060 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21060
  have eq21469 : (σ x) = (k (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21061 eq21046
    | exact resolve eq21046 eq21061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21046 eq21061
  have eq21480 : (σ x) = (k (σ x) (σ x)) ∨ y = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq21469
  have eq21505 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21480 eq1126
    | (have j0 := eq1126 (σ x)
       grind)
    | exact resolve eq1126 eq21480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21480
  have eq21520 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq21505
  have eq21527 : x = (M.op x x) ∨ y = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq21520
    | exact resolve eq21520 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21520
  have eq21533 : y = (k x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq21527
       have r₂ := eq1104
       grind)
    | exact resolve eq21527 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq21527
  have eq21536 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1106
       have i₂ := eq21533
       grind)
    | exact superpose eq21533 eq1106
    | exact resolve eq1106 eq21533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq21541 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6889 x y
       have i₂ := eq21533
       grind)
    | exact superpose eq21533 eq6889
    | (have j0 := eq6889 x x
       grind)
    | exact resolve eq6889 eq21533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6889 eq21533
  have eq21545 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq21541
  have eq21546 : y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq21536
  have eq21549 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq21545
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21545
    | exact resolve eq21545 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21545
  have eq21555 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq21549
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21549
    | exact resolve eq21549 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21549
  have eq21557 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq21555
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21555
    | exact resolve eq21555 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21555
  have eq21558 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq21557
    | exact resolve eq21557 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21557
  have eq21559 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq21558
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21558
    | exact resolve eq21558 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21558
  have eq21560 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20148 eq21559
    | exact resolve eq21559 eq20148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20148 eq21559
  have eq21574 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 y X0
       have i₂ := eq21546
       grind)
    | exact superpose eq21546 eq28
    | (have j0 := eq28 y X0
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq21546
       grind)
    | (have r₁ := eq28 x x
       have r₂ := eq21546
       grind)
    | exact resolve eq28 eq21546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21575 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y
       have i₂ := eq21546
       grind)
    | exact superpose eq21546 eq14
    | (have j0 := eq14 X0 y
       grind)
    | (have r₁ := eq14 X0 y
       have r₂ := eq21546
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq21546
       grind)
    | exact resolve eq14 eq21546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21576 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21575 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21575
  have eq21577 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21574 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21574
  have eq21624 : y = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21546
       have i₂ := eq21576 y
       grind)
    | exact superpose eq21576 eq21546
    | exact resolve eq21546 eq21576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21546 eq21576
  have eq21633 : y = (k y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq21624
  have eq21649 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1129 y X0
       have i₂ := eq21633
       grind)
    | exact superpose eq21633 eq1129
    | (have j0 := eq1129 y X0
       grind)
    | exact resolve eq1129 eq21633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21633
  have eq21658 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21649 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21649
  have eq21667 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21658 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21658
    | (have j0 := eq21658 X0
       grind)
    | exact resolve eq21658 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21658
  have eq21747 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21577 x
       grind)
    | exact superpose eq21577 eq18
    | (have j1 := eq21577 x
       grind)
    | exact resolve eq18 eq21577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21577
  have eq21761 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq21747
       grind)
    | exact superpose eq21747 eq40
    | exact resolve eq40 eq21747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21747
  have eq21766 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21761
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21761
    | exact resolve eq21761 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21761
  have eq21772 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq21766
    | exact resolve eq21766 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21766
  have eq21809 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21667 eq26
    | (have j1 := eq21667 (σ x)
       grind)
    | exact resolve eq26 eq21667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21667
  have eq21822 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20268 eq21809
    | exact resolve eq21809 eq20268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20268 eq21809
  have eq21838 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21822 eq21772
    | exact resolve eq21772 eq21822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21772 eq21822
  have eq21843 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq21838
  have eq21857 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq21843
       have r₂ := eq20710
       grind)
    | exact resolve eq21843 eq20710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21843
  have eq21875 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq21857
       grind)
    | exact superpose eq21857 eq14
    | (have j0 := eq14 X0 x
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq21857
       grind)
    | exact resolve eq14 eq21857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21876 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21875 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21875
  have eq21891 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21876 y
       grind)
    | exact superpose eq21876 eq18
    | (have j1 := eq21876 y
       grind)
    | exact resolve eq18 eq21876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21892 : x = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21857
       have i₂ := eq21876 x
       grind)
    | exact superpose eq21876 eq21857
    | exact resolve eq21857 eq21876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21857 eq21876
  have eq21899 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq21892
  have eq21906 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq21891
       grind)
    | exact superpose eq21891 eq40
    | exact resolve eq40 eq21891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21891
  have eq21910 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21906
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21906
    | exact resolve eq21906 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21906
  have eq21916 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq21910
    | exact resolve eq21910 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21910
  have eq21932 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1127 x X0
       have i₂ := eq21899
       grind)
    | exact superpose eq21899 eq1127
    | (have j0 := eq1127 x X0
       grind)
    | exact resolve eq1127 eq21899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21899
  have eq21945 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21932 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21932
  have eq21953 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21945 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21945
    | (have j0 := eq21945 X0
       grind)
    | exact resolve eq21945 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21945
  have eq22352 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21953 eq26
    | (have j1 := eq21953 (σ y)
       grind)
    | exact resolve eq26 eq21953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21953
  have eq22381 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20707 eq22352
    | exact resolve eq22352 eq20707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20707 eq22352
  have eq22399 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22381 eq21916
    | exact resolve eq21916 eq22381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21916 eq22381
  have eq22404 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq22399
  have eq22420 : y = (M.op x y) := by
    first
    | (have r₁ := eq22404
       have r₂ := eq20710
       grind)
    | exact resolve eq22404 eq20710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20710 eq22404
  have eq22429 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22420
       grind)
    | exact superpose eq22420 eq18
    | exact resolve eq18 eq22420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq22430 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq22420
       grind)
    | exact superpose eq22420 eq24
    | exact resolve eq24 eq22420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq22465 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22430 eq20
    | exact resolve eq20 eq22430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22430
  have eq1857939 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21560 eq14
    | (have j0 := eq14 X0 (σ y)
       grind)
    | (have r₁ := eq14 X0 (σ y)
       have r₂ := eq21560
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq21560
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq21560
       grind)
    | exact resolve eq14 eq21560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1857940 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq1857939 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857939
  have eq4643643 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1857940 eq21560
    | exact resolve eq21560 eq1857940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21560 eq1857940
  have eq4643658 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq4643643
  have eq4643816 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4643658 eq1126
    | (have j0 := eq1126 (σ y)
       grind)
    | exact resolve eq1126 eq4643658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4643658
  have eq4643837 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq4643816
  have eq4643844 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq32 eq4643837
    | exact resolve eq4643837 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4643837
  have eq4643994 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq4643844
       have i₂ := eq22420
       grind)
    | exact superpose eq22420 eq4643844
    | exact resolve eq4643844 eq22420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22420 eq4643844
  have eq4643995 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq4643994
  have eq4644182 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq4643995 eq14
    | (have j0 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq4643995
       grind)
    | (have r₁ := eq14 X0 (M.op x y)
       have r₂ := eq4643995
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq4643995
       grind)
    | exact resolve eq14 eq4643995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4644183 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq4644182 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644182
  have eq4644286 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4644183 eq4643995
    | exact resolve eq4643995 eq4644183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4643995 eq4644183
  have eq4644293 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq4644286
  have eq4644612 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4644293 eq1126
    | (have j0 := eq1126 (σ x)
       grind)
    | exact resolve eq1126 eq4644293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126 eq4644293
  have eq4644633 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq4644612
  have eq4644640 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq4644633
    | exact resolve eq4644633 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4644633
  have eq4644641 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq4644640
  have eq4644721 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq4644641 eq28
    | (have j0 := eq28 (M.op x y) X0
       grind)
    | (have r₁ := eq28 (M.op x y) x
       have r₂ := eq4644641
       grind)
    | (have r₁ := eq28 x x
       have r₂ := eq4644641
       grind)
    | exact resolve eq28 eq4644641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4644722 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq4644641 eq14
    | (have j0 := eq14 X0 (M.op x y)
       grind)
    | (have r₁ := eq14 X0 (M.op x y)
       have r₂ := eq4644641
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq4644641
       grind)
    | exact resolve eq14 eq4644641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4644723 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq4644722 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644722
  have eq4644724 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq4644721 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644721
  have eq4645733 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4644723 eq4644641
    | exact resolve eq4644641 eq4644723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644641 eq4644723
  have eq4645738 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq4645733
  have eq4645902 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq4645738 eq1129
    | (have j0 := eq1129 (M.op x y) X0
       grind)
    | exact resolve eq1129 eq4645738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129 eq4645738
  have eq4645917 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq4645902 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645902
  have eq4645929 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq20 eq4645917
    | (have j0 := eq4645917 X0
       grind)
    | exact resolve eq4645917 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645917
  have eq4646091 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq22465 eq4645929
    | exact resolve eq4645929 eq22465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645929
  have eq4653574 : (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4644724 eq22429
    | exact resolve eq22429 eq4644724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644724
  have eq4653727 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4653574 eq40
    | exact resolve eq40 eq4653574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4653574
  have eq4653732 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq4653727
    | exact resolve eq4653727 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4653727
  have eq4653883 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22465 eq4653732
    | exact resolve eq4653732 eq22465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4653732
  have eq4654764 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4646091 eq26
    | (have j1 := eq4646091 (σ x)
       grind)
    | exact resolve eq26 eq4646091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4646091
  have eq4654784 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4653883 eq4654764
    | exact resolve eq4654764 eq4653883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4653883 eq4654764
  have eq4654785 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4654784
  have eq4654810 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq4654785
       grind)
    | exact superpose eq4654785 eq14
    | (have j0 := eq14 X0 x
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq4654785
       grind)
    | exact resolve eq14 eq4654785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4654811 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq4654810 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654810
  have eq4654832 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4654785
       have i₂ := eq4654811 x
       grind)
    | exact superpose eq4654811 eq4654785
    | exact resolve eq4654785 eq4654811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654785
  have eq4654836 : (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22429
       have i₂ := eq4654811 sF0
       grind)
    | exact superpose eq4654811 eq22429
    | exact resolve eq22429 eq4654811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22429 eq4654811
  have eq4654842 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4654832
  have eq4654996 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4654836 eq40
    | exact resolve eq40 eq4654836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4654836
  have eq4655000 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4654996
    | exact resolve eq4654996 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4654996
  have eq4655151 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22465 eq4655000
    | exact resolve eq4655000 eq22465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4655000
  have eq4655393 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1127 x X0
       have i₂ := eq4654842
       grind)
    | exact superpose eq4654842 eq1127
    | (have j0 := eq1127 x X0
       grind)
    | exact resolve eq1127 eq4654842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127 eq4654842
  have eq4655412 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq4655393 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4655393
  have eq4655423 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4655412 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4655412
    | (have j0 := eq4655412 X0
       grind)
    | exact resolve eq4655412 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4655412
  have eq4656544 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4655423 eq26
    | (have j1 := eq4655423 (σ y)
       grind)
    | exact resolve eq26 eq4655423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4655423
  have eq4656576 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4655151 eq4656544
    | exact resolve eq4656544 eq4655151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4655151 eq4656544
  have eq4656577 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4656576
  have eq4656581 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq4656577 eq27
    | exact resolve eq27 eq4656577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4656577
  have eq4656583 : False := by grind
  exact eq4656583

/-- `x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then m(X,Y) else if m(Y,X) = X then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_pxx_x_pyx_x_pxy_pxy_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X0
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq298 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq382 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq298
    | exact resolve eq298 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq1104 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (k y x) := by
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
  have eq1105 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1106 : (M.op x y) = (k y x) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq1107 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1111 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq14
    | (have j0 := eq14 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq14 X0 X0
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
  have eq1114 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1115 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1116 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1119 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1111 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1120 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1121 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1119 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq1119 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq1119 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1122 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1120 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq1120 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq1120 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1126 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1116 (τ X0)
       have i₂ := eq382 X0 X0
       grind)
    | exact superpose eq382 eq1116
    | (have j0 := eq1116 (τ X0)
       grind)
    | exact resolve eq1116 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq1116
  have eq1127 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1121 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1121
    | (have j0 := eq1121 (σ X0) X1
       grind)
    | exact resolve eq1121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq1129 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1122 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1122
    | (have j0 := eq1122 (σ X0) X1
       grind)
    | exact resolve eq1122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq6607 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1106
       grind)
    | exact superpose eq1106 eq40
    | exact resolve eq40 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq6608 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6607
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6607
    | exact resolve eq6607 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6607
  have eq6612 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq6608
    | exact resolve eq6608 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6608
  have eq6889 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1114 (σ X1) (σ X0)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1114
    | (have j0 := eq1114 (σ X0) (σ X0)
       grind)
    | exact resolve eq1114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq19377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6612 eq1107
    | exact resolve eq1107 eq6612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107 eq6612
  have eq19390 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq19377
       have r₂ := eq27
       grind)
    | exact resolve eq19377 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19377
  have eq19781 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq19390 eq14
    | (have j0 := eq14 X0 (σ y)
       grind)
    | (have r₁ := eq14 X0 (σ y)
       have r₂ := eq19390
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq19390
       grind)
    | (have r₁ := eq14 X0 y
       have r₂ := eq19390
       grind)
    | exact resolve eq14 eq19390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19782 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq19781 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19781
  have eq19794 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq19782 eq19390
    | exact resolve eq19390 eq19782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19390 eq19782
  have eq19795 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq19794
  have eq19818 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq19795 eq1126
    | (have j0 := eq1126 (σ y)
       grind)
    | exact resolve eq1126 eq19795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19795
  have eq19833 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq19818
  have eq19840 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq32 eq19833
    | exact resolve eq19833 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19833
  have eq19841 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq19840
  have eq19854 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq19841 eq14
    | (have j0 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq19841
       grind)
    | (have r₁ := eq14 X0 y
       have r₂ := eq19841
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq19841
       grind)
    | exact resolve eq14 eq19841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19855 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq19854 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19854
  have eq20023 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq19855 eq19841
    | exact resolve eq19841 eq19855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19841 eq19855
  have eq20024 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq20023
  have eq20037 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20024 eq1126
    | (have j0 := eq1126 (σ x)
       grind)
    | exact resolve eq1126 eq20024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20024
  have eq20052 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq20037
  have eq20059 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq20052
    | exact resolve eq20052 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20052
  have eq20060 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq20059
  have eq20074 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y
       have i₂ := eq20060
       grind)
    | exact superpose eq20060 eq14
    | (have j0 := eq14 X0 y
       grind)
    | (have r₁ := eq14 X0 y
       have r₂ := eq20060
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq20060
       grind)
    | exact resolve eq14 eq20060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20075 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20074 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20074
  have eq20141 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20075 x
       grind)
    | exact superpose eq20075 eq18
    | (have j1 := eq20075 x
       grind)
    | exact resolve eq18 eq20075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20142 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20060
       have i₂ := eq20075 y
       grind)
    | exact superpose eq20075 eq20060
    | exact resolve eq20060 eq20075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20060 eq20075
  have eq20143 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq20142
  have eq20151 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq20141
       grind)
    | exact superpose eq20141 eq41
    | exact resolve eq41 eq20141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20141
  have eq20156 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20151
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20151
    | exact resolve eq20151 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20151
  have eq20162 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq20156
    | exact resolve eq20156 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20156
  have eq20178 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1127 y X0
       have i₂ := eq20143
       grind)
    | exact superpose eq20143 eq1127
    | (have j0 := eq1127 y X0
       grind)
    | exact resolve eq1127 eq20143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20143
  have eq20191 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20178 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20178
  have eq20199 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20191 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20191
    | (have j0 := eq20191 X0
       grind)
    | exact resolve eq20191 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20191
  have eq20303 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20199 eq26
    | (have j1 := eq20199 (σ x)
       grind)
    | exact resolve eq26 eq20199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20199
  have eq20310 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20162 eq20303
    | exact resolve eq20303 eq20162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20162 eq20303
  have eq20312 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20310
       have r₂ := eq27
       grind)
    | exact resolve eq20310 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20310
  have eq20319 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 x X0
       have i₂ := eq20312
       grind)
    | exact superpose eq20312 eq28
    | (have j0 := eq28 x X0
       grind)
    | (have r₁ := eq28 x x
       have r₂ := eq20312
       grind)
    | exact resolve eq28 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20320 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq20312
       grind)
    | exact superpose eq20312 eq14
    | (have j0 := eq14 X0 x
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq20312
       grind)
    | exact resolve eq14 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20321 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20320 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20320
  have eq20322 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20319 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20319
  have eq20334 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20312
       have i₂ := eq20321 x
       grind)
    | exact superpose eq20321 eq20312
    | exact resolve eq20312 eq20321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20321
  have eq20335 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20334
  have eq20349 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1129 x X0
       have i₂ := eq20335
       grind)
    | exact superpose eq20335 eq1129
    | (have j0 := eq1129 x X0
       grind)
    | exact resolve eq1129 eq20335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20351 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6889 x x
       have i₂ := eq20335
       grind)
    | exact superpose eq20335 eq6889
    | (have j0 := eq6889 x x
       grind)
    | exact resolve eq6889 eq20335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20335
  have eq20355 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20351
  have eq20356 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20355
  have eq20358 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20349 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20349
  have eq20366 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20356
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20356
    | exact resolve eq20356 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20356
  have eq20367 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20358 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20358
    | (have j0 := eq20358 X0
       grind)
    | exact resolve eq20358 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20358
  have eq20667 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20322 y
       grind)
    | exact superpose eq20322 eq18
    | (have j1 := eq20322 y
       grind)
    | exact resolve eq18 eq20322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20322
  have eq20679 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq20667
       grind)
    | exact superpose eq20667 eq41
    | exact resolve eq41 eq20667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20667
  have eq20683 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20679
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20679
    | exact resolve eq20679 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20679
  have eq20689 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq20683
    | exact resolve eq20683 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20683
  have eq20715 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20367 eq26
    | (have j1 := eq20367 (σ y)
       grind)
    | exact resolve eq26 eq20367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20367
  have eq20729 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20689 eq20715
    | exact resolve eq20715 eq20689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20689 eq20715
  have eq20731 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20729
       have r₂ := eq27
       grind)
    | exact resolve eq20729 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20729
  have eq20733 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20731 eq1105
    | (have r₁ := eq1105
       have r₂ := eq20731
       grind)
    | exact resolve eq1105 eq20731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq20734 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20731 eq27
    | exact resolve eq27 eq20731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20735 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20733
  have eq20941 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20735 eq142
    | exact resolve eq142 eq20735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq20735
  have eq20952 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq20941
    | exact resolve eq20941 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20941
  have eq20968 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20952 eq14
    | (have j0 := eq14 X0 (σ y)
       grind)
    | (have r₁ := eq14 X0 (σ y)
       have r₂ := eq20952
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq20952
       grind)
    | exact resolve eq14 eq20952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20969 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20968 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20968
  have eq21037 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20969 eq20952
    | exact resolve eq20952 eq20969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20952 eq20969
  have eq21042 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq21037
  have eq21057 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21042 eq1126
    | (have j0 := eq1126 (σ y)
       grind)
    | exact resolve eq1126 eq21042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21042
  have eq21072 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq21057
  have eq21079 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq21072
    | exact resolve eq21072 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21072
  have eq21378 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op y y) ∨ y = (k y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21079 eq14
    | (have j0 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq21079
       grind)
    | (have r₁ := eq14 X0 y
       have r₂ := eq21079
       grind)
    | exact resolve eq14 eq21079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21379 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op y y) ∨ y = (k y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21378 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21378
  have eq21509 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21379 eq21079
    | exact resolve eq21079 eq21379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21079 eq21379
  have eq21516 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq21509
  have eq21539 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21516 eq1126
    | (have j0 := eq1126 (σ x)
       grind)
    | exact resolve eq1126 eq21516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21516
  have eq21554 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y y) ∨ y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq21539
  have eq21561 : x = (M.op x x) ∨ y = (M.op y y) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq21554
    | exact resolve eq21554 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21554
  have eq21567 : y = (k y x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq21561
       have r₂ := eq1104
       grind)
    | exact resolve eq21561 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq21561
  have eq21570 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1106
       have i₂ := eq21567
       grind)
    | exact superpose eq21567 eq1106
    | exact resolve eq1106 eq21567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq21575 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6889 y x
       have i₂ := eq21567
       grind)
    | exact superpose eq21567 eq6889
    | (have j0 := eq6889 y y
       grind)
    | exact resolve eq6889 eq21567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6889 eq21567
  have eq21579 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq21575
  have eq21580 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq21570
  have eq21583 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21579
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21579
    | exact resolve eq21579 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21579
  have eq21589 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21583
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21583
    | exact resolve eq21583 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21583
  have eq21591 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21589
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21589
    | exact resolve eq21589 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21589
  have eq21592 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq21591
    | exact resolve eq21591 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21591
  have eq21593 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21592
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21592
    | exact resolve eq21592 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21592
  have eq21594 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20366 eq21593
    | exact resolve eq21593 eq20366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20366 eq21593
  have eq21609 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y
       have i₂ := eq21580
       grind)
    | exact superpose eq21580 eq14
    | (have j0 := eq14 X0 y
       grind)
    | (have r₁ := eq14 X0 y
       have r₂ := eq21580
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq21580
       grind)
    | exact resolve eq14 eq21580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21610 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq21609 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21609
  have eq21664 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21610 x
       grind)
    | exact superpose eq21610 eq18
    | (have j1 := eq21610 x
       grind)
    | exact resolve eq18 eq21610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21665 : y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21580
       have i₂ := eq21610 y
       grind)
    | exact superpose eq21610 eq21580
    | exact resolve eq21580 eq21610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21580 eq21610
  have eq21670 : y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq21665
  have eq21680 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq21664
       grind)
    | exact superpose eq21664 eq41
    | exact resolve eq41 eq21664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21664
  have eq21685 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21680
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21680
    | exact resolve eq21680 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21680
  have eq21691 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq21685
    | exact resolve eq21685 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21685
  have eq21707 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1127 y X0
       have i₂ := eq21670
       grind)
    | exact superpose eq21670 eq1127
    | (have j0 := eq1127 y X0
       grind)
    | exact resolve eq1127 eq21670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21670
  have eq21720 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq21707 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21707
  have eq21728 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq21720 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21720
    | (have j0 := eq21720 X0
       grind)
    | exact resolve eq21720 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21720
  have eq21872 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21728 eq26
    | (have j1 := eq21728 (σ x)
       grind)
    | exact resolve eq26 eq21728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21728
  have eq21885 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20312 eq21872
    | exact resolve eq21872 eq20312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20312 eq21872
  have eq21901 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21885 eq21691
    | exact resolve eq21691 eq21885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21691 eq21885
  have eq21906 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq21901
  have eq21920 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq21906
       have r₂ := eq20734
       grind)
    | exact resolve eq21906 eq20734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21906
  have eq21940 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 x X0
       have i₂ := eq21920
       grind)
    | exact superpose eq21920 eq28
    | (have j0 := eq28 x X0
       grind)
    | (have r₁ := eq28 x x
       have r₂ := eq21920
       grind)
    | exact resolve eq28 eq21920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21941 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq21920
       grind)
    | exact superpose eq21920 eq14
    | (have j0 := eq14 X0 x
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq21920
       grind)
    | exact resolve eq14 eq21920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21942 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21941 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21941
  have eq21943 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21940 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21940
  have eq21960 : x = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21920
       have i₂ := eq21942 x
       grind)
    | exact superpose eq21942 eq21920
    | exact resolve eq21920 eq21942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21920 eq21942
  have eq21963 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq21960
  have eq21978 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1129 x X0
       have i₂ := eq21963
       grind)
    | exact superpose eq21963 eq1129
    | (have j0 := eq1129 x X0
       grind)
    | exact resolve eq1129 eq21963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21963
  have eq21987 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21978 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21978
  have eq21996 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21987 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21987
    | (have j0 := eq21987 X0
       grind)
    | exact resolve eq21987 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21987
  have eq22067 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21943 y
       grind)
    | exact superpose eq21943 eq18
    | (have j1 := eq21943 y
       grind)
    | exact resolve eq18 eq21943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21943
  have eq22082 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq22067
       grind)
    | exact superpose eq22067 eq41
    | exact resolve eq41 eq22067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq22067
  have eq22086 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22082
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22082
    | exact resolve eq22082 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22082
  have eq22092 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq22086
    | exact resolve eq22086 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22086
  have eq22378 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21996 eq26
    | (have j1 := eq21996 (σ y)
       grind)
    | exact resolve eq26 eq21996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21996
  have eq22407 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20731 eq22378
    | exact resolve eq22378 eq20731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20731 eq22378
  have eq22425 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22407 eq22092
    | exact resolve eq22092 eq22407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22092 eq22407
  have eq22430 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq22425
  have eq22446 : y = (M.op x y) := by
    first
    | (have r₁ := eq22430
       have r₂ := eq20734
       grind)
    | exact resolve eq22430 eq20734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20734 eq22430
  have eq22459 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22446
       grind)
    | exact superpose eq22446 eq18
    | exact resolve eq18 eq22446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq22460 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq22446
       grind)
    | exact superpose eq22446 eq24
    | exact resolve eq24 eq22446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq22495 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22460 eq20
    | exact resolve eq20 eq22460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22460
  have eq1857879 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq21594 eq14
    | (have j0 := eq14 X0 (σ y)
       grind)
    | (have r₁ := eq14 X0 (σ y)
       have r₂ := eq21594
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq21594
       grind)
    | (have r₁ := eq14 X0 (M.op x y)
       have r₂ := eq21594
       grind)
    | exact resolve eq14 eq21594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1857880 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1857879 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857879
  have eq4643463 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1857880 eq21594
    | exact resolve eq21594 eq1857880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21594 eq1857880
  have eq4643474 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq4643463
  have eq4643866 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4643474 eq1126
    | (have j0 := eq1126 (σ y)
       grind)
    | exact resolve eq1126 eq4643474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4643474
  have eq4643887 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq4643866
  have eq4643894 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq32 eq4643887
    | exact resolve eq4643887 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4643887
  have eq4644044 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4643894
       have i₂ := eq22446
       grind)
    | exact superpose eq22446 eq4643894
    | exact resolve eq4643894 eq22446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22446 eq4643894
  have eq4644045 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq4644044
  have eq4644232 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq4644045 eq14
    | (have j0 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq4644045
       grind)
    | (have r₁ := eq14 X0 (M.op x y)
       have r₂ := eq4644045
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq4644045
       grind)
    | exact resolve eq14 eq4644045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4644233 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq4644232 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644232
  have eq4644338 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4644233 eq4644045
    | exact resolve eq4644045 eq4644233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644045 eq4644233
  have eq4644341 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq4644338
  have eq4644427 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4644341 eq1126
    | (have j0 := eq1126 (σ x)
       grind)
    | exact resolve eq1126 eq4644341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126 eq4644341
  have eq4644448 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq4644427
  have eq4644455 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq4644448
    | exact resolve eq4644448 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4644448
  have eq4644456 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq4644455
  have eq4644537 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq4644456 eq14
    | (have j0 := eq14 X0 (M.op x y)
       grind)
    | (have r₁ := eq14 X0 (M.op x y)
       have r₂ := eq4644456
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq4644456
       grind)
    | exact resolve eq14 eq4644456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4644538 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq4644537 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644537
  have eq4645554 : (M.op x y) = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4644538 eq22459
    | exact resolve eq22459 eq4644538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4645555 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4644538 eq4644456
    | exact resolve eq4644456 eq4644538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644456 eq4644538
  have eq4645556 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq4645555
  have eq4645718 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq4645556 eq1127
    | (have j0 := eq1127 (M.op x y) X0
       grind)
    | exact resolve eq1127 eq4645556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127 eq4645556
  have eq4645737 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq4645718 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645718
  have eq4645748 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq20 eq4645737
    | (have j0 := eq4645737 X0
       grind)
    | exact resolve eq4645737 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645737
  have eq4645910 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq22495 eq4645748
    | exact resolve eq4645748 eq22495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645748
  have eq4646281 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4645554 eq36
    | exact resolve eq36 eq4645554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645554
  have eq4646296 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq4646281
    | exact resolve eq4646281 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4646281
  have eq4646447 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22495 eq4646296
    | exact resolve eq4646296 eq22495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4646296
  have eq4654568 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4645910 eq26
    | (have j1 := eq4645910 (σ x)
       grind)
    | exact resolve eq26 eq4645910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645910
  have eq4654588 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4646447 eq4654568
    | exact resolve eq4654568 eq4646447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4646447 eq4654568
  have eq4654589 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4654588
  have eq4654613 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28 x X0
       have i₂ := eq4654589
       grind)
    | exact superpose eq4654589 eq28
    | (have j0 := eq28 x X0
       grind)
    | (have r₁ := eq28 x x
       have r₂ := eq4654589
       grind)
    | exact resolve eq28 eq4654589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4654614 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq4654589
       grind)
    | exact superpose eq4654589 eq14
    | (have j0 := eq14 X0 x
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq4654589
       grind)
    | exact resolve eq14 eq4654589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4654615 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq4654614 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654614
  have eq4654616 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq4654613 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654613
  have eq4654638 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4654589
       have i₂ := eq4654615 x
       grind)
    | exact superpose eq4654615 eq4654589
    | exact resolve eq4654589 eq4654615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654589 eq4654615
  have eq4654642 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4654638
  have eq4654727 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1129 x X0
       have i₂ := eq4654642
       grind)
    | exact superpose eq4654642 eq1129
    | (have j0 := eq1129 x X0
       grind)
    | exact resolve eq1129 eq4654642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129 eq4654642
  have eq4654742 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq4654727 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654727
  have eq4654754 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4654742 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4654742
    | (have j0 := eq4654742 X0
       grind)
    | exact resolve eq4654742 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4654742
  have eq4655206 : (M.op x y) = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22459
       have i₂ := eq4654616 sF0
       grind)
    | exact superpose eq4654616 eq22459
    | exact resolve eq22459 eq4654616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22459 eq4654616
  have eq4655361 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4655206 eq36
    | exact resolve eq36 eq4655206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq4655206
  have eq4655375 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4655361
    | exact resolve eq4655361 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4655361
  have eq4655526 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22495 eq4655375
    | exact resolve eq4655375 eq22495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4655375
  have eq4656219 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4654754 eq26
    | (have j1 := eq4654754 (σ y)
       grind)
    | exact resolve eq26 eq4654754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4654754
  have eq4656251 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4655526 eq4656219
    | exact resolve eq4656219 eq4655526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4655526 eq4656219
  have eq4656252 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4656251
  have eq4656256 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq4656252 eq27
    | exact resolve eq27 eq4656252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4656252
  have eq4656258 : False := by grind
  exact eq4656258

/-- `x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then m(X,Y) else if m(Y,X) = Y then Y
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_pxx_x_pyx_y_pxy_pxy_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq67 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq36
  have eq78 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq16
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : x ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (k y x) := by
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
  have eq85 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq66
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq66
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq66 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq98 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq67
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq67 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq98
  have eq110 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq95
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq124 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq154 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq156 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq125
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq125
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq156
  have eq182 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq200 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq523 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq89 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq3001 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq154 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq154
    | (have j0 := eq154 x
       grind)
    | exact resolve eq154 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq3007 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3001
  have eq3011 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3007
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3007
    | exact resolve eq3007 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3007
  have eq3028 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | (have r₁ := eq3011
       have r₂ := eq14 x (σ x)
       grind)
    | exact resolve eq3011 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011
  have eq3035 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3028 eq49
    | exact resolve eq49 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq3161 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq182 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq182
    | (have j0 := eq182 y
       grind)
    | exact resolve eq182 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq3166 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3161
  have eq3169 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3166
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq3166
    | exact resolve eq3166 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3166
  have eq3193 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | (have r₁ := eq3169
       have r₂ := eq14 x (σ y)
       grind)
    | exact resolve eq3169 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3169
  have eq3217 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3193 eq78
    | exact resolve eq78 eq3193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3343 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq200
    | (have j0 := eq200 (M.op x y)
       grind)
    | exact resolve eq200 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq3347 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3343
  have eq3349 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq125 eq3347
    | exact resolve eq3347 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq3347
  have eq3380 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq14 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq3349
       have r₂ := eq14 x (σ (M.op x y))
       grind)
    | exact resolve eq3349 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349
  have eq3420 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3380 eq159
    | exact resolve eq159 eq3380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq8261 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3193 eq109
    | exact resolve eq109 eq3193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq8262 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3028 eq110
    | exact resolve eq110 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq8785 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3380 eq164
    | exact resolve eq164 eq3380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq3380
  have eq11134 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq8261
       grind)
    | exact superpose eq8261 eq16
    | exact resolve eq16 eq8261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8261
  have eq11183 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3217 eq11134
    | exact resolve eq11134 eq3217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11134
  have eq11186 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq14 y y
       grind)
    | (have r₁ := eq11183
       have r₂ := eq14 x y
       grind)
    | exact resolve eq11183 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11183
  have eq11187 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq11186
       grind)
    | exact superpose eq11186 eq67
    | exact resolve eq67 eq11186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq11212 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq3193 eq11187
    | exact resolve eq11187 eq3193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3193 eq11187
  have eq11219 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq8262
       grind)
    | exact superpose eq8262 eq16
    | exact resolve eq16 eq8262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8262
  have eq11270 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3035 eq11219
    | exact resolve eq11219 eq3035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11219
  have eq11273 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq14 x x
       grind)
    | (have r₁ := eq11270
       have r₂ := eq14 x x
       grind)
    | exact resolve eq11270 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11270
  have eq11274 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11273
       grind)
    | exact superpose eq11273 eq43
    | exact resolve eq43 eq11273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq11299 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq3028 eq11274
    | exact resolve eq11274 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3028 eq11274
  have eq11860 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8785 eq16
    | exact resolve eq16 eq8785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8785
  have eq11915 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3420 eq11860
    | exact resolve eq11860 eq3420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11860
  have eq11918 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq14 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq11915
       have r₂ := eq14 x (M.op x y)
       grind)
    | exact resolve eq11915 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11915
  have eq18430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq18430
    | exact resolve eq18430 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18430
  have eq18442 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq18431
       have r₂ := eq27
       grind)
    | exact resolve eq18431 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18431
  have eq18446 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq18442
    | exact resolve eq18442 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18442
  have eq18448 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq18446 eq3217
    | exact resolve eq3217 eq18446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18446
  have eq18469 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18448
       have i₂ := eq11186
       grind)
    | exact superpose eq11186 eq18448
    | exact resolve eq18448 eq11186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18448
  have eq18478 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq18469
    | exact resolve eq18469 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18469
  have eq18479 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq18478
  have eq18481 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq18479 eq3035
    | exact resolve eq3035 eq18479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18479
  have eq18502 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18481
       have i₂ := eq11273
       grind)
    | exact superpose eq11273 eq18481
    | exact resolve eq18481 eq11273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18481
  have eq18511 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq18502
    | exact resolve eq18502 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18502
  have eq18512 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq18511
  have eq18520 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11212
       have i₂ := eq18512
       grind)
    | exact superpose eq18512 eq11212
    | exact resolve eq11212 eq18512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18524 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y
       have i₂ := eq18512
       grind)
    | exact superpose eq18512 eq14
    | (have j0 := eq14 X0 y
       grind)
    | (have r₁ := eq14 X0 y
       have r₂ := eq18512
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq18512
       grind)
    | exact resolve eq14 eq18512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18512
  have eq18525 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18524 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18524
  have eq18529 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18520
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18520
    | exact resolve eq18520 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18520
  have eq18825 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18529 eq14
    | (have j0 := eq14 X0 (σ y)
       grind)
    | (have r₁ := eq14 X0 (σ y)
       have r₂ := eq18529
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq18529
       grind)
    | exact resolve eq14 eq18529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18529
  have eq18826 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18825 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18825
  have eq18864 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq18525 x
       grind)
    | exact superpose eq18525 eq44
    | exact resolve eq44 eq18525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18525
  have eq18947 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18864
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18864
    | exact resolve eq18864 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18864
  have eq18963 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq18947
    | exact resolve eq18947 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18947
  have eq19453 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18826 eq18963
    | exact resolve eq18963 eq18826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18826 eq18963
  have eq19488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq19453
  have eq19501 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19488
    | exact resolve eq19488 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19488
  have eq19515 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19501
       have r₂ := eq27
       grind)
    | exact resolve eq19501 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19501
  have eq19803 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11299
       have i₂ := eq19515
       grind)
    | exact superpose eq19515 eq11299
    | exact resolve eq11299 eq19515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19806 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59 x X0
       have i₂ := eq19515
       grind)
    | exact superpose eq19515 eq59
    | (have j0 := eq59 x X0
       grind)
    | (have r₁ := eq59 x x
       have r₂ := eq19515
       grind)
    | exact resolve eq59 eq19515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19515
  have eq19809 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19806 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19806
  have eq19812 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq19830 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq19812 eq59
    | (have j0 := eq59 (σ x) X0
       grind)
    | (have r₁ := eq59 (σ x) x
       have r₂ := eq19812
       grind)
    | exact resolve eq59 eq19812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19812
  have eq19833 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19830 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19830
  have eq20307 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq19809 y
       grind)
    | exact superpose eq19809 eq44
    | exact resolve eq44 eq19809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19809
  have eq20336 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20307
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20307
    | exact resolve eq20307 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20307
  have eq20368 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq20336
    | exact resolve eq20336 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20336
  have eq20879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19833 eq20368
    | exact resolve eq20368 eq19833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19833 eq20368
  have eq20880 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20879
  have eq20884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq20880
    | exact resolve eq20880 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20880
  have eq20909 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20884
       have r₂ := eq27
       grind)
    | exact resolve eq20884 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20884
  have eq21194 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20909 eq85
    | (have r₁ := eq85
       have r₂ := eq20909
       grind)
    | exact resolve eq85 eq20909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq21195 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20909 eq27
    | exact resolve eq27 eq20909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20909
  have eq21196 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq21194
  have eq36515 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21196 eq3217
    | exact resolve eq3217 eq21196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21196
  have eq36536 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36515
       have i₂ := eq11186
       grind)
    | exact superpose eq11186 eq36515
    | exact resolve eq36515 eq11186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36515
  have eq36545 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq36536
    | exact resolve eq36536 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36536
  have eq36553 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36545 eq115
    | exact resolve eq115 eq36545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq36545
  have eq36566 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq36553
  have eq36577 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq36566
       have r₂ := eq21195
       grind)
    | exact resolve eq36566 eq21195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21195 eq36566
  have eq36871 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36577 eq3035
    | exact resolve eq3035 eq36577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035 eq36577
  have eq36892 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36871
       have i₂ := eq11273
       grind)
    | exact superpose eq11273 eq36871
    | exact resolve eq36871 eq11273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11273 eq36871
  have eq36901 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq36892
    | exact resolve eq36892 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq36892
  have eq36902 : y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq36901
  have eq36910 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11212
       have i₂ := eq36902
       grind)
    | exact superpose eq36902 eq11212
    | exact resolve eq11212 eq36902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36914 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y
       have i₂ := eq36902
       grind)
    | exact superpose eq36902 eq14
    | (have j0 := eq14 X0 y
       grind)
    | (have r₁ := eq14 X0 y
       have r₂ := eq36902
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq36902
       grind)
    | exact resolve eq14 eq36902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36902
  have eq36915 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq36914 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36914
  have eq36919 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36910
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36910
    | exact resolve eq36910 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36910
  have eq36938 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36919 eq14
    | (have j0 := eq14 X0 (σ y)
       grind)
    | (have r₁ := eq14 X0 (σ y)
       have r₂ := eq36919
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq36919
       grind)
    | exact resolve eq14 eq36919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36919
  have eq36939 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq36938 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36938
  have eq37283 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq36915 x
       grind)
    | exact superpose eq36915 eq44
    | exact resolve eq44 eq36915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36915
  have eq37442 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37283
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37283
    | exact resolve eq37283 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37283
  have eq37458 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq37442
    | exact resolve eq37442 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37442
  have eq38051 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36939 eq37458
    | exact resolve eq37458 eq36939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36939 eq37458
  have eq38120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq38051
  have eq38141 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq38120
    | exact resolve eq38120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38120
  have eq38155 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq38141
       have r₂ := eq27
       grind)
    | exact resolve eq38141 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38141
  have eq38163 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11299
       have i₂ := eq38155
       grind)
    | exact superpose eq38155 eq11299
    | exact resolve eq11299 eq38155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38166 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59 x X0
       have i₂ := eq38155
       grind)
    | exact superpose eq38155 eq59
    | (have j0 := eq59 x X0
       grind)
    | (have r₁ := eq59 x x
       have r₂ := eq38155
       grind)
    | exact resolve eq59 eq38155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38155
  have eq38169 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq38166 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38166
  have eq38172 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38163
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38163
    | exact resolve eq38163 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38163
  have eq38478 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38172 eq59
    | (have j0 := eq59 (σ x) X0
       grind)
    | (have r₁ := eq59 (σ x) x
       have r₂ := eq38172
       grind)
    | exact resolve eq59 eq38172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38172
  have eq38481 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq38478 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38478
  have eq39100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq38169 y
       grind)
    | exact superpose eq38169 eq44
    | exact resolve eq44 eq38169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38169
  have eq39135 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq39100
    | exact resolve eq39100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39100
  have eq39196 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq39135
    | exact resolve eq39135 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39135
  have eq39798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38481 eq39196
    | exact resolve eq39196 eq38481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38481 eq39196
  have eq39799 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq39798
  have eq39807 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq39799
    | exact resolve eq39799 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39799
  have eq39832 : x = (M.op x y) := by
    first
    | (have r₁ := eq39807
       have r₂ := eq27
       grind)
    | exact resolve eq39807 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39807
  have eq39834 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq39832 eq20
    | exact resolve eq20 eq39832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39841 : x ≠ x ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq39832 eq84
    | (have r₁ := eq84
       have r₂ := eq39832
       grind)
    | exact resolve eq84 eq39832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq39943 : y = (M.op y y) ∨ x = (M.op x x) ∨ x = (k y x) := by grind
  clear eq39841
  have eq40050 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq39834
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39834
    | exact resolve eq39834 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39834
  have eq40093 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq40050 eq26
    | exact resolve eq26 eq40050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46364 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11212
       have i₂ := eq39943
       grind)
    | exact superpose eq39943 eq11212
    | exact resolve eq11212 eq39943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46368 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y
       have i₂ := eq39943
       grind)
    | exact superpose eq39943 eq14
    | (have j0 := eq14 X0 y
       grind)
    | (have r₁ := eq14 X0 y
       have r₂ := eq39943
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq39943
       grind)
    | exact resolve eq14 eq39943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39943
  have eq46369 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) ∨ x = (k y x) := by
    intro X0
    first
    | (have j0 := eq46368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46368
  have eq46373 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq46364
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq46364
    | exact resolve eq46364 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46364
  have eq46396 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (k y x) := by
    intro X0
    first
    | exact superpose eq46373 eq14
    | (have j0 := eq14 X0 (σ y)
       grind)
    | (have r₁ := eq14 X0 (σ y)
       have r₂ := eq46373
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq46373
       grind)
    | exact resolve eq14 eq46373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46373
  have eq46397 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ x = (k y x) := by
    intro X0
    first
    | (have j0 := eq46396 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46396
  have eq62452 : (σ (M.op (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq124
       have i₂ := eq46369 sF0
       grind)
    | exact superpose eq46369 eq124
    | exact resolve eq124 eq46369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46369
  have eq62618 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq39832 eq62452
    | exact resolve eq62452 eq39832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62452
  have eq62713 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq62618
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq62618
    | exact resolve eq62618 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62618
  have eq62754 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq20 eq62713
    | exact resolve eq62713 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62713
  have eq64931 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) ∨ x = (k y x) ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq46397 eq62754
    | exact resolve eq62754 eq46397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46397 eq62754
  have eq65031 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) ∨ x = (k y x) := by grind
  clear eq64931
  have eq65095 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq40093 eq65031
    | exact resolve eq65031 eq40093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65031
  have eq65131 : x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq65095
       have r₂ := eq27
       grind)
    | exact resolve eq65095 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65095
  have eq65178 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq523 x y
       have i₂ := eq65131
       grind)
    | exact superpose eq65131 eq523
    | (have j0 := eq523 y y
       grind)
    | exact resolve eq523 eq65131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523 eq65131
  have eq65181 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq65178
  have eq65189 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65181
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq65181
    | exact resolve eq65181 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65181
  have eq65204 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65189
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq65189
    | exact resolve eq65189 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65189
  have eq65218 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65204
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq65204
    | exact resolve eq65204 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65204
  have eq65228 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq65218
    | exact resolve eq65218 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq65218
  have eq65232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40050 eq65228
    | exact resolve eq65228 eq40050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65228
  have eq65233 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq65232
       have r₂ := eq27
       grind)
    | exact resolve eq65232 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65232
  have eq65234 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65233
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq65233
    | exact resolve eq65233 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65233
  have eq65235 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40050 eq65234
    | exact resolve eq65234 eq40050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65234
  have eq65536 : (τ (σ y)) = (k y y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq65235 eq3217
    | exact resolve eq3217 eq65235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3217 eq65235
  have eq65557 : (τ (σ y)) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65536
       have i₂ := eq11186
       grind)
    | exact superpose eq11186 eq65536
    | exact resolve eq65536 eq11186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11186 eq65536
  have eq65566 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq65557
    | exact resolve eq65557 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq65557
  have eq65572 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq65566 eq3420
    | exact resolve eq3420 eq65566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3420 eq65566
  have eq65593 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq11918 eq65572
    | exact resolve eq65572 eq11918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11918 eq65572
  have eq65602 : (τ (σ (M.op x y))) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq39832 eq65593
    | exact resolve eq65593 eq39832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65593
  have eq65611 : (M.op x y) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq65602
    | exact resolve eq65602 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq65602
  have eq65620 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq39832 eq65611
    | exact resolve eq65611 eq39832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65611
  have eq65621 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq65620
  have eq65633 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11212
       have i₂ := eq65621
       grind)
    | exact superpose eq65621 eq11212
    | exact resolve eq11212 eq65621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11212
  have eq65641 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y
       have i₂ := eq65621
       grind)
    | exact superpose eq65621 eq14
    | (have j0 := eq14 X0 y
       grind)
    | (have r₁ := eq14 X0 y
       have r₂ := eq65621
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq65621
       grind)
    | exact resolve eq14 eq65621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65621
  have eq65642 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq65641 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65641
  have eq65650 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65633
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq65633
    | exact resolve eq65633 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq65633
  have eq65673 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq65650 eq14
    | (have j0 := eq14 X0 (σ y)
       grind)
    | (have r₁ := eq14 X0 (σ y)
       have r₂ := eq65650
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq65650
       grind)
    | exact resolve eq14 eq65650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65650
  have eq65674 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq65673 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65673
  have eq65770 : (σ (M.op (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq124
       have i₂ := eq65642 sF0
       grind)
    | exact superpose eq65642 eq124
    | exact resolve eq124 eq65642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq65642
  have eq65942 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq39832 eq65770
    | exact resolve eq65770 eq39832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39832 eq65770
  have eq66037 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65942
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq65942
    | exact resolve eq65942 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65942
  have eq66078 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq66037
    | exact resolve eq66037 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66037
  have eq69027 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq65674 eq66078
    | exact resolve eq66078 eq65674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65674 eq66078
  have eq69129 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq69027
  have eq69199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40093 eq69129
    | exact resolve eq69129 eq40093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69129
  have eq69235 : x = (M.op x x) := by
    first
    | (have r₁ := eq69199
       have r₂ := eq27
       grind)
    | exact resolve eq69199 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69199
  have eq69262 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11299
       have i₂ := eq69235
       grind)
    | exact superpose eq69235 eq11299
    | exact resolve eq11299 eq69235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11299
  have eq69269 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq59 x X0
       have i₂ := eq69235
       grind)
    | exact superpose eq69235 eq59
    | (have j0 := eq59 x X0
       grind)
    | (have r₁ := eq59 x x
       have r₂ := eq69235
       grind)
    | exact resolve eq59 eq69235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69235
  have eq69272 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq69269 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69269
  have eq69279 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq40050 eq69262
    | exact resolve eq69262 eq40050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69262
  have eq69292 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq69279
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq69279
    | exact resolve eq69279 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq69279
  have eq69301 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq40050 eq69292
    | exact resolve eq69292 eq40050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69292
  have eq69322 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq69301 eq59
    | (have j0 := eq59 (σ (M.op x y)) X0
       grind)
    | (have r₁ := eq59 (σ (M.op x y)) x
       have r₂ := eq69301
       grind)
    | exact resolve eq59 eq69301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq69301
  have eq69325 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq69322 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69322
  have eq70094 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq69272 y
       grind)
    | exact superpose eq69272 eq44
    | exact resolve eq44 eq69272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq69272
  have eq70142 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq40050 eq70094
    | exact resolve eq70094 eq40050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40050 eq70094
  have eq70270 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq70142
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq70142
    | exact resolve eq70142 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq70142
  have eq70375 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq70270
    | exact resolve eq70270 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq70270
  have eq71270 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq69325 eq70375
    | exact resolve eq70375 eq69325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69325 eq70375
  have eq71271 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40093 eq71270
    | exact resolve eq71270 eq40093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40093 eq71270
  have eq71369 : False := by grind
  exact eq71369

/-- `x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then m(X,Y) else if X = Y then m(X,X)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_pxx_x_x_y_pxy_pxy_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq29 : ∀ X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
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
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  clear eq45
  have eq61 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    first
    | (have j0 := eq29 X1
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq29 X1
       have r₂ := eq14 x X1
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq61 (σ X0)
       grind)
    | exact superpose eq61 eq10
    | exact resolve eq10 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq51
       have i₂ := eq61 sF2
       grind)
    | exact superpose eq61 eq51
    | exact resolve eq51 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq65
       have i₂ := eq61 x
       grind)
    | exact superpose eq61 eq65
    | exact resolve eq65 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq63
    | exact resolve eq63 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq84 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq86 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq61 sF3
       grind)
    | exact superpose eq61 eq84
    | exact resolve eq84 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq88 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq86
       have i₂ := eq61 y
       grind)
    | exact superpose eq61 eq86
    | exact resolve eq86 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq86
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq83
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq106
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq118 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq419 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq72
    | (have j0 := eq72 (σ X0) X1
       grind)
    | exact resolve eq72 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq15933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq15934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq15933
    | exact resolve eq15933 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15933
  have eq15945 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq15934
       have r₂ := eq28
       grind)
    | exact resolve eq15934 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15934
  have eq15951 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq15945 eq118
    | exact resolve eq118 eq15945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq15945
  have eq15972 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq31 eq15951
    | exact resolve eq15951 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15951
  have eq15973 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq15972
  have eq15978 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq15973 eq66
    | exact resolve eq66 eq15973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15973
  have eq16003 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq15978
    | exact resolve eq15978 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15978
  have eq16004 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq16003
  have eq16017 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq420 y X0
       have i₂ := eq16004
       grind)
    | exact superpose eq16004 eq420
    | (have j0 := eq420 y X0
       grind)
    | exact resolve eq420 eq16004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq16020 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 X0 y
       have i₂ := eq16004
       grind)
    | exact superpose eq16004 eq14
    | (have j0 := eq14 X0 y
       grind)
    | (have r₁ := eq14 X0 y
       have r₂ := eq16004
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq16004
       grind)
    | exact resolve eq14 eq16004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16004
  have eq16021 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16020 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16020
  have eq16024 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16017 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16017
  have eq16026 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16024 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16024
    | (have j0 := eq16024 X0
       grind)
    | exact resolve eq16024 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16024
  have eq16083 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq46
       have i₂ := eq16021 x
       grind)
    | exact superpose eq16021 eq46
    | exact resolve eq46 eq16021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16021
  have eq16145 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16083
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16083
    | exact resolve eq16083 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16083
  have eq16155 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq16145
    | exact resolve eq16145 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16145
  have eq16387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16026 eq16155
    | exact resolve eq16155 eq16026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16026 eq16155
  have eq16411 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq16387
  have eq16424 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16411
    | exact resolve eq16411 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16411
  have eq16435 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16424
       have r₂ := eq28
       grind)
    | exact resolve eq16424 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16424
  have eq16448 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq419 x X0
       have i₂ := eq16435
       grind)
    | exact superpose eq16435 eq419
    | (have j0 := eq419 x X0
       grind)
    | exact resolve eq419 eq16435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq16449 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq72 x X0
       have i₂ := eq16435
       grind)
    | exact superpose eq16435 eq72
    | (have j0 := eq72 x X0
       grind)
    | (have r₁ := eq72 x x
       have r₂ := eq16435
       grind)
    | exact resolve eq72 eq16435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq16435
  have eq16452 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16449 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16449
  have eq16453 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16448 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16448
  have eq16455 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16453 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16453
    | (have j0 := eq16453 X0
       grind)
    | exact resolve eq16453 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16453
  have eq16853 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq46
       have i₂ := eq16452 y
       grind)
    | exact superpose eq16452 eq46
    | exact resolve eq46 eq16452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq16452
  have eq16885 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16853
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16853
    | exact resolve eq16853 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16853
  have eq16906 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq16885
    | exact resolve eq16885 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16885
  have eq17276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16455 eq16906
    | exact resolve eq16906 eq16455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16455 eq16906
  have eq17277 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17276
  have eq17281 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq17277
    | exact resolve eq17277 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17277
  have eq17304 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17281
       have r₂ := eq28
       grind)
    | exact resolve eq17281 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17281
  have eq17551 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq17304 eq31
    | exact resolve eq31 eq17304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq17304
  have eq17675 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq17551
    | exact resolve eq17551 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17551
  have eq17676 : x = y := by grind
  clear eq17675
  have eq17695 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq17676
       grind)
    | exact superpose eq17676 eq19
    | exact resolve eq19 eq17676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq17696 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq17676
       grind)
    | exact superpose eq17676 eq25
    | exact resolve eq25 eq17676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17676
  have eq17829 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17696
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17696
    | exact resolve eq17696 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17696
  have eq17850 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17829 eq27
    | exact resolve eq27 eq17829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17829
  have eq18475 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17850 eq66
    | exact resolve eq66 eq17850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq17850
  have eq18498 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18475
       have i₂ := eq17695
       grind)
    | exact superpose eq17695 eq18475
    | exact resolve eq18475 eq17695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17695 eq18475
  have eq18505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18498 eq15
    | exact resolve eq15 eq18498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18498
  have eq18594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18505
    | exact resolve eq18505 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18505
  have eq18616 : False := by grind
  exact eq18616

/-- `x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then m(X,Y) else if X = Y then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_pxx_x_x_y_pxy_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq29 : ∀ X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
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
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  clear eq45
  have eq61 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    first
    | (have j0 := eq29 X1
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq29 X1
       have r₂ := eq14 x X1
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq61 (σ X0)
       grind)
    | exact superpose eq61 eq10
    | exact resolve eq10 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq51
       have i₂ := eq61 sF2
       grind)
    | exact superpose eq61 eq51
    | exact resolve eq51 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq65
       have i₂ := eq61 x
       grind)
    | exact superpose eq61 eq65
    | exact resolve eq65 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq63
    | exact resolve eq63 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq84 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq86 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq61 sF3
       grind)
    | exact superpose eq61 eq84
    | exact resolve eq84 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq88 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq86
       have i₂ := eq61 y
       grind)
    | exact superpose eq61 eq86
    | exact resolve eq86 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq86
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq83
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq106
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq118 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq419 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq72
    | (have j0 := eq72 (σ X0) X1
       grind)
    | exact resolve eq72 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq15933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq15934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq15933
    | exact resolve eq15933 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15933
  have eq15945 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq15934
       have r₂ := eq28
       grind)
    | exact resolve eq15934 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15934
  have eq15951 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq15945 eq118
    | exact resolve eq118 eq15945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq15945
  have eq15972 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq31 eq15951
    | exact resolve eq15951 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15951
  have eq15973 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq15972
  have eq15978 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq15973 eq66
    | exact resolve eq66 eq15973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15973
  have eq16003 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq15978
    | exact resolve eq15978 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15978
  have eq16004 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq16003
  have eq16017 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq420 y X0
       have i₂ := eq16004
       grind)
    | exact superpose eq16004 eq420
    | (have j0 := eq420 y X0
       grind)
    | exact resolve eq420 eq16004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq16020 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 X0 y
       have i₂ := eq16004
       grind)
    | exact superpose eq16004 eq14
    | (have j0 := eq14 X0 y
       grind)
    | (have r₁ := eq14 X0 y
       have r₂ := eq16004
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq16004
       grind)
    | exact resolve eq14 eq16004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16004
  have eq16021 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16020 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16020
  have eq16024 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16017 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16017
  have eq16026 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16024 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16024
    | (have j0 := eq16024 X0
       grind)
    | exact resolve eq16024 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16024
  have eq16083 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq46
       have i₂ := eq16021 x
       grind)
    | exact superpose eq16021 eq46
    | exact resolve eq46 eq16021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16021
  have eq16145 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16083
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16083
    | exact resolve eq16083 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16083
  have eq16155 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq16145
    | exact resolve eq16145 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16145
  have eq16387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16026 eq16155
    | exact resolve eq16155 eq16026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16026 eq16155
  have eq16411 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq16387
  have eq16424 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16411
    | exact resolve eq16411 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16411
  have eq16435 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16424
       have r₂ := eq28
       grind)
    | exact resolve eq16424 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16424
  have eq16448 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq419 x X0
       have i₂ := eq16435
       grind)
    | exact superpose eq16435 eq419
    | (have j0 := eq419 x X0
       grind)
    | exact resolve eq419 eq16435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq16449 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq72 x X0
       have i₂ := eq16435
       grind)
    | exact superpose eq16435 eq72
    | (have j0 := eq72 x X0
       grind)
    | (have r₁ := eq72 x x
       have r₂ := eq16435
       grind)
    | exact resolve eq72 eq16435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq16435
  have eq16452 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16449 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16449
  have eq16453 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16448 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16448
  have eq16455 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16453 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16453
    | (have j0 := eq16453 X0
       grind)
    | exact resolve eq16453 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16453
  have eq16853 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq46
       have i₂ := eq16452 y
       grind)
    | exact superpose eq16452 eq46
    | exact resolve eq46 eq16452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq16452
  have eq16885 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16853
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16853
    | exact resolve eq16853 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16853
  have eq16906 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq16885
    | exact resolve eq16885 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16885
  have eq17276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16455 eq16906
    | exact resolve eq16906 eq16455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16455 eq16906
  have eq17277 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17276
  have eq17281 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq17277
    | exact resolve eq17277 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17277
  have eq17304 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17281
       have r₂ := eq28
       grind)
    | exact resolve eq17281 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17281
  have eq17551 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq17304 eq31
    | exact resolve eq31 eq17304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq17304
  have eq17675 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq17551
    | exact resolve eq17551 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17551
  have eq17676 : x = y := by grind
  clear eq17675
  have eq17695 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq17676
       grind)
    | exact superpose eq17676 eq19
    | exact resolve eq19 eq17676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq17696 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq17676
       grind)
    | exact superpose eq17676 eq25
    | exact resolve eq25 eq17676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17676
  have eq17829 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17696
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17696
    | exact resolve eq17696 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17696
  have eq17850 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17829 eq27
    | exact resolve eq27 eq17829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17829
  have eq18475 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17850 eq66
    | exact resolve eq66 eq17850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq17850
  have eq18498 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18475
       have i₂ := eq17695
       grind)
    | exact superpose eq17695 eq18475
    | exact resolve eq18475 eq17695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17695 eq18475
  have eq18505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18498 eq15
    | exact resolve eq15 eq18498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18498
  have eq18594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18505
    | exact resolve eq18505 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18505
  have eq18616 : False := by grind
  exact eq18616

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then m(Y,X) else if X = Y then m(X,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_pxx_x_x_y_pyx_pyx_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq29 : ∀ X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
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
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  clear eq45
  have eq61 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    first
    | (have j0 := eq29 X1
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq29 X1
       have r₂ := eq14 x X1
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq61 (σ X0)
       grind)
    | exact superpose eq61 eq10
    | exact resolve eq10 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq51
       have i₂ := eq61 sF2
       grind)
    | exact superpose eq61 eq51
    | exact resolve eq51 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq65
       have i₂ := eq61 x
       grind)
    | exact superpose eq61 eq65
    | exact resolve eq65 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq63
    | exact resolve eq63 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq84 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq86 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq61 sF3
       grind)
    | exact superpose eq61 eq84
    | exact resolve eq84 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq88 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq86
       have i₂ := eq61 y
       grind)
    | exact superpose eq61 eq86
    | exact resolve eq86 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq86
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107
    | exact resolve eq107 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq113
    | exact resolve eq113 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq119 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq419 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq72
    | (have j0 := eq72 (σ X0) X1
       grind)
    | exact resolve eq72 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq15933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq15934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq15933
    | exact resolve eq15933 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15933
  have eq15945 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq15934
       have r₂ := eq28
       grind)
    | exact resolve eq15934 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15934
  have eq15951 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq15945 eq119
    | exact resolve eq119 eq15945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq15945
  have eq15972 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq15951
    | exact resolve eq15951 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15951
  have eq15973 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq15972
  have eq15978 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq15973 eq66
    | exact resolve eq66 eq15973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15973
  have eq16003 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq30 eq15978
    | exact resolve eq15978 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15978
  have eq16004 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq16003
  have eq16018 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq419 y X0
       have i₂ := eq16004
       grind)
    | exact superpose eq16004 eq419
    | (have j0 := eq419 y X0
       grind)
    | exact resolve eq419 eq16004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq16019 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq72 y X0
       have i₂ := eq16004
       grind)
    | exact superpose eq16004 eq72
    | (have j0 := eq72 y X0
       grind)
    | (have r₁ := eq72 y x
       have r₂ := eq16004
       grind)
    | (have r₁ := eq72 x x
       have r₂ := eq16004
       grind)
    | exact resolve eq72 eq16004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq16004
  have eq16022 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16019 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16019
  have eq16023 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16018 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16018
  have eq16025 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16023 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16023
    | (have j0 := eq16023 X0
       grind)
    | exact resolve eq16023 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16023
  have eq16175 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq83
       have i₂ := eq16022 x
       grind)
    | exact superpose eq16022 eq83
    | exact resolve eq83 eq16022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16022
  have eq16204 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16175
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16175
    | exact resolve eq16175 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16175
  have eq16224 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq16204
    | exact resolve eq16204 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16204
  have eq16339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16025 eq16224
    | exact resolve eq16224 eq16025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16025 eq16224
  have eq16340 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq16339
  have eq16342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16340
    | exact resolve eq16340 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16340
  have eq16364 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16342
       have r₂ := eq28
       grind)
    | exact resolve eq16342 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16342
  have eq16376 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq420 x X0
       have i₂ := eq16364
       grind)
    | exact superpose eq16364 eq420
    | (have j0 := eq420 x X0
       grind)
    | exact resolve eq420 eq16364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq16379 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq16364
       grind)
    | exact superpose eq16364 eq14
    | (have j0 := eq14 X0 x
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq16364
       grind)
    | exact resolve eq14 eq16364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16364
  have eq16380 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16379
  have eq16383 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16376 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16376
  have eq16385 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16383 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16383
    | (have j0 := eq16383 X0
       grind)
    | exact resolve eq16383 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16383
  have eq16683 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq83
       have i₂ := eq16380 y
       grind)
    | exact superpose eq16380 eq83
    | exact resolve eq83 eq16380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq16380
  have eq16750 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16683
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16683
    | exact resolve eq16683 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16683
  have eq16761 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq16750
    | exact resolve eq16750 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16750
  have eq17253 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16385 eq16761
    | exact resolve eq16761 eq16385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16385 eq16761
  have eq17279 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17253
  have eq17294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq17279
    | exact resolve eq17279 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17279
  have eq17306 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17294
       have r₂ := eq28
       grind)
    | exact resolve eq17294 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17294
  have eq17553 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq17306 eq31
    | exact resolve eq31 eq17306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq17306
  have eq17677 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq17553
    | exact resolve eq17553 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17553
  have eq17678 : x = y := by grind
  clear eq17677
  have eq17697 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq17678
       grind)
    | exact superpose eq17678 eq19
    | exact resolve eq19 eq17678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq17698 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq17678
       grind)
    | exact superpose eq17678 eq25
    | exact resolve eq25 eq17678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17678
  have eq17831 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17698
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17698
    | exact resolve eq17698 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17698
  have eq17852 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17831 eq27
    | exact resolve eq27 eq17831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17831
  have eq18477 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17852 eq66
    | exact resolve eq66 eq17852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq17852
  have eq18500 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18477
       have i₂ := eq17697
       grind)
    | exact superpose eq17697 eq18477
    | exact resolve eq18477 eq17697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17697 eq18477
  have eq18507 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18500 eq15
    | exact resolve eq15 eq18500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18500
  have eq18596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18507
    | exact resolve eq18507 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18507
  have eq18618 : False := by grind
  exact eq18618

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then m(Y,X) else if X = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_pxx_x_x_y_pyx_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq29 : ∀ X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
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
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  clear eq45
  have eq61 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    first
    | (have j0 := eq29 X1
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq29 X1
       have r₂ := eq14 x X1
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq61 (σ X0)
       grind)
    | exact superpose eq61 eq10
    | exact resolve eq10 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq51
       have i₂ := eq61 sF2
       grind)
    | exact superpose eq61 eq51
    | exact resolve eq51 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq65
       have i₂ := eq61 x
       grind)
    | exact superpose eq61 eq65
    | exact resolve eq65 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq63
    | exact resolve eq63 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq84 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq86 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq61 sF3
       grind)
    | exact superpose eq61 eq84
    | exact resolve eq84 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq88 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq86
       have i₂ := eq61 y
       grind)
    | exact superpose eq61 eq86
    | exact resolve eq86 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq86
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107
    | exact resolve eq107 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq113
    | exact resolve eq113 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq119 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq419 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq72
    | (have j0 := eq72 (σ X0) X1
       grind)
    | exact resolve eq72 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq15933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq15934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq15933
    | exact resolve eq15933 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15933
  have eq15945 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq15934
       have r₂ := eq28
       grind)
    | exact resolve eq15934 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15934
  have eq15951 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq15945 eq119
    | exact resolve eq119 eq15945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq15945
  have eq15972 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq15951
    | exact resolve eq15951 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15951
  have eq15973 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq15972
  have eq15978 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq15973 eq66
    | exact resolve eq66 eq15973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15973
  have eq16003 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq30 eq15978
    | exact resolve eq15978 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15978
  have eq16004 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq16003
  have eq16018 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq419 y X0
       have i₂ := eq16004
       grind)
    | exact superpose eq16004 eq419
    | (have j0 := eq419 y X0
       grind)
    | exact resolve eq419 eq16004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq16019 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq72 y X0
       have i₂ := eq16004
       grind)
    | exact superpose eq16004 eq72
    | (have j0 := eq72 y X0
       grind)
    | (have r₁ := eq72 y x
       have r₂ := eq16004
       grind)
    | (have r₁ := eq72 x x
       have r₂ := eq16004
       grind)
    | exact resolve eq72 eq16004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq16004
  have eq16022 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16019 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16019
  have eq16023 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16018 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16018
  have eq16025 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16023 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16023
    | (have j0 := eq16023 X0
       grind)
    | exact resolve eq16023 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16023
  have eq16175 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq83
       have i₂ := eq16022 x
       grind)
    | exact superpose eq16022 eq83
    | exact resolve eq83 eq16022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16022
  have eq16204 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16175
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16175
    | exact resolve eq16175 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16175
  have eq16224 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq16204
    | exact resolve eq16204 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16204
  have eq16339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16025 eq16224
    | exact resolve eq16224 eq16025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16025 eq16224
  have eq16340 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq16339
  have eq16342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq16340
    | exact resolve eq16340 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16340
  have eq16364 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16342
       have r₂ := eq28
       grind)
    | exact resolve eq16342 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16342
  have eq16376 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq420 x X0
       have i₂ := eq16364
       grind)
    | exact superpose eq16364 eq420
    | (have j0 := eq420 x X0
       grind)
    | exact resolve eq420 eq16364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq16379 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq16364
       grind)
    | exact superpose eq16364 eq14
    | (have j0 := eq14 X0 x
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq16364
       grind)
    | exact resolve eq14 eq16364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16364
  have eq16380 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16379
  have eq16383 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16376 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16376
  have eq16385 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16383 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16383
    | (have j0 := eq16383 X0
       grind)
    | exact resolve eq16383 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16383
  have eq16683 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq83
       have i₂ := eq16380 y
       grind)
    | exact superpose eq16380 eq83
    | exact resolve eq83 eq16380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq16380
  have eq16750 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16683
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16683
    | exact resolve eq16683 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16683
  have eq16761 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq16750
    | exact resolve eq16750 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16750
  have eq17253 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16385 eq16761
    | exact resolve eq16761 eq16385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16385 eq16761
  have eq17279 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17253
  have eq17294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq17279
    | exact resolve eq17279 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17279
  have eq17306 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17294
       have r₂ := eq28
       grind)
    | exact resolve eq17294 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17294
  have eq17553 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq17306 eq31
    | exact resolve eq31 eq17306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq17306
  have eq17677 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq17553
    | exact resolve eq17553 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17553
  have eq17678 : x = y := by grind
  clear eq17677
  have eq17697 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq17678
       grind)
    | exact superpose eq17678 eq19
    | exact resolve eq19 eq17678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq17698 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq17678
       grind)
    | exact superpose eq17678 eq25
    | exact resolve eq25 eq17678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17678
  have eq17831 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17698
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17698
    | exact resolve eq17698 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17698
  have eq17852 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17831 eq27
    | exact resolve eq27 eq17831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17831
  have eq18477 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17852 eq66
    | exact resolve eq66 eq17852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq17852
  have eq18500 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18477
       have i₂ := eq17697
       grind)
    | exact superpose eq17697 eq18477
    | exact resolve eq18477 eq17697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17697 eq18477
  have eq18507 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18500 eq15
    | exact resolve eq15 eq18500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18500
  have eq18596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18507
    | exact resolve eq18507 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18507
  have eq18618 : False := by grind
  exact eq18618
