import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then m(Y,X) else if X = Y then m(Y,Y)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_pxx_x_x_y_pyx_pyx_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ a ≠ b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
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

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then Y else if m(Y,X) = Y then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_pyx_x_pyx_y_pyx_y_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq31 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17 (σ y) (σ x)
       grind)
    | exact superpose eq17 eq16
    | (have j1 := eq17 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq17 X0 X0
       grind)
    | exact superpose eq17 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq17 X0 X0
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq17 X0 X0
       grind)
    | exact resolve eq11 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq17 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq35 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq38 : (M.op (σ x) (σ y)) = (σ (k y (τ (σ x)))) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq31
    | exact resolve eq31 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq40 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq38
    | exact resolve eq38 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq45 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq37 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq17 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq17 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq17 X0 X0
       grind)
    | exact resolve eq13 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq57 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq34 X0 X1
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq34 (k X1 X0) X1
       grind)
    | (have r₁ := eq56 X0 X0
       have r₂ := eq34 X0 (k X0 X0)
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq34 X0 X1
       grind)
    | exact resolve eq56 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq56
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq57 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq57 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq61 : ∀ X0 : G, (σ (k X0 (τ (σ X0)))) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 (σ X0) X0
       have i₂ := eq46 (σ X0)
       grind)
    | exact superpose eq46 eq19
    | exact resolve eq19 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq64
    | exact resolve eq64 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq86 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq11
    | (have j0 := eq11 X1 (σ X0)
       grind)
    | exact resolve eq11 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 (τ X1))) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 (σ X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq58
    | (have j0 := eq58 X1 (σ X0)
       grind)
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (τ X0) = (τ (k X0 (σ X1))) ∨ (τ X0) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1 (τ X0)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq58
    | (have j0 := eq58 X1 (τ X0)
       grind)
    | exact resolve eq58 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40
       have i₂ := eq17 y x
       grind)
    | exact superpose eq17 eq40
    | (have j1 := eq17 y x
       grind)
    | exact resolve eq40 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq111 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq110
  have eq120 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq95
    | (have j0 := eq95 X1 (σ X0)
       grind)
    | exact resolve eq95 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq154 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (k X1 X0)) ∨ (τ X1) = (τ (k X1 X0)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96
    | (have j0 := eq96 X1 (τ X0)
       grind)
    | exact resolve eq96 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (τ X1) = (τ (k X1 (σ X0))) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (σ X0))
       have i₂ := eq96 X1 X0
       grind)
    | exact superpose eq96 eq10
    | (have j1 := eq96 X1 X0
       grind)
    | exact resolve eq10 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq192 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X0)
       have i₂ := eq120 X0 X1
       grind)
    | exact superpose eq120 eq9
    | (have j1 := eq120 X0 X1
       grind)
    | exact resolve eq9 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (τ (k X1 X0)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq154 X0 X1
       grind)
    | exact superpose eq154 eq10
    | (have j1 := eq154 X0 X1
       grind)
    | exact resolve eq10 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq394 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (τ (k (σ X0) (σ X1))) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq163 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq163
    | exact resolve eq163 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k (τ X0) X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (τ X0) = (τ (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq163 X1 X0
       grind)
    | exact superpose eq163 eq12
    | (have j0 := eq12 (τ X0) X1
       have j1 := eq163 X1 X0
       grind)
    | (have r₁ := eq12 (τ X1) X0
       have r₂ := eq163 X0 X1
       grind)
    | exact resolve eq12 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq409 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (τ X0) = (τ (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq407 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq418 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (τ (k X0 (σ X1))) = X1 ∨ (τ X0) = (τ (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq409
    | (have j0 := eq409 X0 X1
       grind)
    | exact resolve eq409 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq428 : ∀ X0 X1 : G, (τ (σ (k X0 (τ (σ X1))))) = X0 ∨ (M.op X1 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq394 X0 X1
       have i₂ := eq19 (σ X1) X0
       grind)
    | exact superpose eq19 eq394
    | (have j0 := eq394 X0 X1
       grind)
    | exact resolve eq394 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq441 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = X0 ∨ (M.op X1 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq428 X0 X1
       have i₂ := eq9 (k X0 (τ (σ X1)))
       grind)
    | exact superpose eq9 eq428
    | (have j0 := eq428 X0 X1
       grind)
    | exact resolve eq428 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq451 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq441
    | (have j0 := eq441 X0 X1
       grind)
    | exact resolve eq441 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq461 : ∀ X0 X1 : G, (σ (k X0 (τ (σ X1)))) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 X1
       have i₂ := eq19 (σ X1) X0
       grind)
    | exact superpose eq19 eq451
    | (have j0 := eq451 X0 X1
       grind)
    | exact resolve eq451 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq470 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq461 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq461
    | (have j0 := eq461 X0 X1
       grind)
    | exact resolve eq461 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq487 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq192 X1 X0
       grind)
    | exact superpose eq192 eq9
    | (have j1 := eq192 X1 X0
       grind)
    | exact resolve eq9 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq491 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq487 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq487
    | (have j0 := eq487 X0 X1
       grind)
    | exact resolve eq487 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq597 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (τ (M.op (σ X1) (σ (τ X0)))) ∨ (τ X0) = (τ (k X0 (σ X1))) ∨ (σ (τ X0)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq491 (τ X0) X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq491
    | (have j0 := eq491 (τ X0) X1
       grind)
    | exact resolve eq491 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (σ (τ (M.op (σ X0) (σ X1)))) ∨ (τ (M.op (σ X0) (σ X1))) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq470 X0 X1
       have i₂ := eq491 X0 X1
       grind)
    | exact superpose eq491 eq470
    | (have j0 := eq470 X1 X0
       have j1 := eq491 X1 X0
       grind)
    | exact resolve eq470 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq618 : ∀ X0 X1 : G, (τ (M.op (σ X1) (σ X0))) ≠ X0 ∨ (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq491 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq627 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (σ (τ (M.op (σ X0) (σ X1)))) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq610 X0 X1
       have j1 := eq618 X1 X0
       grind)
    | (have r₁ := eq610 X1 X0
       have r₂ := eq618 X0 X1
       grind)
    | exact resolve eq610 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610 eq618
  have eq634 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (τ (M.op (σ X1) X0)) ∨ (τ X0) = (τ (k X0 (σ X1))) ∨ (σ (τ X0)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq597 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq597
    | (have j0 := eq597 X0 X1
       grind)
    | exact resolve eq597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq639 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq627 X0 X1
       have i₂ := eq10 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq10 eq627
    | (have j0 := eq627 X0 X1
       grind)
    | exact resolve eq627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq642 : ∀ X0 X1 : G, (M.op (σ X1) X0) = X0 ∨ (τ (k X0 (σ X1))) = (τ (M.op (σ X1) X0)) ∨ (τ X0) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq634 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq634
    | (have j0 := eq634 X0 X1
       grind)
    | exact resolve eq634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq1778 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq642 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq642
    | exact resolve eq642 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1792 : (σ (M.op x y)) ≠ (σ y) ∨ (τ (M.op (σ x) (σ y))) = (τ (k (σ y) (σ x))) ∨ (τ (k (σ y) (σ x))) = (τ (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq642 (σ y) x
       grind)
    | exact superpose eq642 eq16
    | (have j1 := eq642 (σ y) x
       grind)
    | exact resolve eq16 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq1819 : (τ (M.op (σ x) (σ y))) = (τ (σ (k y (τ (σ x))))) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (τ (k (σ y) (σ x))) = (τ (σ y)) := by
    first
    | (have i₁ := eq1792
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq1792
    | exact resolve eq1792 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq1830 : (k y (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (τ (k (σ y) (σ x))) = (τ (σ y)) := by
    first
    | (have i₁ := eq1819
       have i₂ := eq9 (k y (τ (σ x)))
       grind)
    | exact superpose eq9 eq1819
    | exact resolve eq1819 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1819
  have eq1841 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (τ (k (σ y) (σ x))) = (τ (σ y)) := by
    first
    | (have i₁ := eq1830
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1830
    | exact resolve eq1830 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1830
  have eq1851 : y = (τ (k (σ y) (σ x))) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq1841
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1841
    | exact resolve eq1841 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841
  have eq1861 : y = (τ (σ (k y (τ (σ x))))) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq1851
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq1851
    | exact resolve eq1851 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851
  have eq1865 : y = (k y (τ (σ x))) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq1861
       have i₂ := eq9 (k y (τ (σ x)))
       grind)
    | exact superpose eq9 eq1861
    | exact resolve eq1861 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861
  have eq1866 : (σ (M.op x y)) ≠ (σ y) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1865
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1865
    | exact resolve eq1865 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1865
  have eq1953 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq1778 X0 X1
       grind)
    | exact superpose eq1778 eq10
    | (have j1 := eq1778 X0 X1
       grind)
    | exact resolve eq10 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1981 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1953 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq1953
    | (have j0 := eq1953 X0 X1
       grind)
    | exact resolve eq1953 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq2113 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (τ (σ X0)) = (τ (σ (k X0 (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1981 X0 (σ X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1981
    | (have j0 := eq1981 X1 (σ X0)
       grind)
    | exact resolve eq1981 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2146 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2113 X0 X1
       have i₂ := eq9 (k X0 (τ X1))
       grind)
    | exact superpose eq9 eq2113
    | (have j0 := eq2113 X0 X1
       grind)
    | exact resolve eq2113 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113
  have eq2148 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (k X0 (τ X1)) = X0 ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2146 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2146
    | (have j0 := eq2146 X0 X1
       grind)
    | exact resolve eq2146 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2465 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2148 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2148
    | (have j0 := eq2148 X1 (σ X0)
       grind)
    | exact resolve eq2148 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148
  have eq2614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2465 x y
       have i₂ := eq111
       grind)
    | exact superpose eq111 eq2465
    | (have j0 := eq2465 x y
       grind)
    | exact resolve eq2465 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq2614
  have eq2664 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq2655
       have r₂ := eq16
       grind)
    | exact resolve eq2655 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2655
  have eq2732 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq40
       have i₂ := eq2664
       grind)
    | exact superpose eq2664 eq40
    | exact resolve eq40 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2664
  have eq2735 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2732
  have eq4576 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X2 (σ X0))) = X0 ∨ (τ X2) = (τ (k X2 (σ X0))) ∨ (k X2 (σ X0)) = (σ (M.op X0 (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq418 X2 X0
       grind)
    | exact superpose eq418 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq418 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq418 X0 X1
       grind)
    | exact resolve eq11 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4578 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (τ (k X2 (σ X0))) = X0 ∨ (τ X2) = (τ (k X2 (σ X0))) ∨ (k X2 (σ X0)) = (σ (M.op X0 (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq418 X2 X0
       grind)
    | exact superpose eq418 eq86
    | (have j0 := eq86 X0 X1
       have j1 := eq418 X2 X0
       grind)
    | exact resolve eq86 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq4598 : ∀ X0 X1 X2 : G, (k X2 (σ X0)) = (σ (M.op X0 (τ X2))) ∨ (τ (k X2 (σ X0))) = X0 ∨ (τ X2) = (τ (k X2 (σ X0))) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4578 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4578
  have eq4600 : ∀ X0 X1 X2 : G, (k X2 (σ X0)) = (σ (M.op X0 (τ X2))) ∨ (τ (k X2 (σ X0))) = X0 ∨ (τ X2) = (τ (k X2 (σ X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4576 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4576
  have eq4637 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq639 x y
       grind)
    | exact superpose eq639 eq111
    | (have j1 := eq639 x y
       grind)
    | exact resolve eq111 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq639
  have eq4638 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq4637
  have eq4645 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4638
       have r₂ := eq16
       grind)
    | exact resolve eq4638 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4638
  have eq4856 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq4645
       grind)
    | exact superpose eq4645 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq4645
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq4645
       grind)
    | exact resolve eq12 eq4645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4857 : x = (M.op x x) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4856
  have eq4918 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11 X0 x
       have i₂ := eq4857
       grind)
    | exact superpose eq4857 eq11
    | (have j0 := eq11 X0 x
       grind)
    | (have r₁ := eq11 X0 x
       have r₂ := eq4857
       grind)
    | exact resolve eq11 eq4857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4857
  have eq4931 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq4918 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4918
  have eq5038 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq4931 X0
       grind)
    | exact superpose eq4931 eq12
    | (have j0 := eq12 (σ y) (σ x)
       have j1 := eq4931 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq4931 X0
       grind)
    | exact resolve eq12 eq4931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4931
  have eq5039 : ∀ X0 : G, (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq5038 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5038
  have eq5040 : ∀ X0 : G, (σ x) = (σ (k y (τ (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq5039 X0
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq5039
    | (have j0 := eq5039 X0
       grind)
    | exact resolve eq5039 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5039
  have eq5042 : ∀ X0 : G, (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq5040 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq5040
    | (have j0 := eq5040 X0
       grind)
    | exact resolve eq5040 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5040
  have eq5043 : ∀ X0 : G, (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) ∨ x = (k y x) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq5042 X0
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq5042
    | (have j0 := eq5042 X0
       grind)
    | exact resolve eq5042 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5042
  have eq7939 : ∀ X0 : G, (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ (k y x)) ∨ x = (k y x) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq5043 X0
       grind)
    | exact superpose eq5043 eq9
    | (have j1 := eq5043 X0
       grind)
    | exact resolve eq9 eq5043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5043
  have eq7956 : ∀ X0 : G, x = (M.op x x) ∨ (σ x) = (σ (k y x)) ∨ x = (k y x) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq7939 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq7939
    | (have j0 := eq7939 X0
       grind)
    | exact resolve eq7939 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7939
  have eq7957 : ∀ X0 : G, (σ x) = (σ (k y x)) ∨ x = (k y x) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq7956 X0
       have j1 := eq11 X0 x
       grind)
    | (have r₁ := eq7956 X0
       have r₂ := eq11 X0 x
       grind)
    | exact resolve eq7956 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7956
  have eq8030 : ∀ X0 : G, (τ (σ x)) = (k y x) ∨ x = (k y x) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq7957 X0
       grind)
    | exact superpose eq7957 eq9
    | (have j1 := eq7957 X0
       grind)
    | exact resolve eq9 eq7957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7957
  have eq8044 : ∀ X0 : G, x = (k y x) ∨ x = (k y x) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq8030 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq8030
    | (have j0 := eq8030 X0
       grind)
    | exact resolve eq8030 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8030
  have eq8045 : ∀ X0 : G, x = (k y x) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq8044 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8044
  have eq8151 : ∀ X0 : G, y = (M.op x y) ∨ (k X0 x) = (M.op x X0) ∨ y = (k y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8045 X0
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq8045
    | (have j0 := eq8045 X0
       have j1 := eq58 x y
       grind)
    | exact resolve eq8045 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8202 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have j0 := eq8045 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8582 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ y = (k y x) ∨ (k X0 x) = (M.op x X0) ∨ y = (k y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1866
       have i₂ := eq8151 X0
       grind)
    | exact superpose eq8151 eq1866
    | (have j1 := eq8151 X0
       grind)
    | exact resolve eq1866 eq8151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866 eq8151
  have eq8602 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k y x) = (τ (M.op (σ x) (σ y))) ∨ y = (k y x) ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8582 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8582
  have eq8603 : ∀ X0 : G, x = (M.op x y) ∨ y = (k y x) ∨ (k X0 x) = (M.op x X0) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq8602 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8602
  have eq15139 : ∀ X0 : G, x ≠ x ∨ y = (k y x) ∨ x = y ∨ x = (M.op x x) ∨ y = (k y x) ∨ (k X0 x) = (M.op x X0) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq13 y x
       have i₂ := eq8603 X0
       grind)
    | exact superpose eq8603 eq13
    | (have j0 := eq13 y x
       have j1 := eq8603 X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8603 X0
       grind)
    | exact resolve eq13 eq8603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8603
  have eq15146 : ∀ X0 : G, x ≠ x ∨ y = (k y x) ∨ x = y ∨ x = (M.op x x) ∨ (k X0 x) = (M.op x X0) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq15139 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15139
  have eq15147 : ∀ X0 : G, y = (k y x) ∨ x = y ∨ x = (M.op x x) ∨ (k X0 x) = (M.op x X0) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq15146 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15146
  have eq15160 : ∀ X0 : G, x = y ∨ y = (k y x) ∨ (k X0 x) = (M.op x X0) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq15147 X0
       have j1 := eq11 X0 x
       grind)
    | (have r₁ := eq15147 X0
       have r₂ := eq11 X0 x
       grind)
    | exact resolve eq15147 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15147
  have eq15423 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (k X0 x) = (M.op x X0) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq15160 X0
       grind)
    | exact superpose eq15160 eq16
    | (have j1 := eq15160 X0
       grind)
    | exact resolve eq16 eq15160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15160
  have eq15539 : ∀ X0 : G, y = (k y x) ∨ (k X0 x) = (M.op x X0) ∨ (k y x) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq15423 X0
       grind)
    | (have r₁ := eq15423 X0
       have r₂ := eq68 x
       grind)
    | exact resolve eq15423 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15423
  have eq15684 : ∀ X0 X1 : G, x = y ∨ (k X0 x) = (M.op x X0) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (k X1 x) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15539 X0
       have i₂ := eq8045 X0
       grind)
    | exact superpose eq8045 eq15539
    | (have j0 := eq15539 X0
       have j1 := eq8045 X0
       grind)
    | exact resolve eq15539 eq8045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15539
  have eq15955 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k X0 x) = (M.op x X0) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (k X1 x) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq15684 X0 X1
       grind)
    | exact superpose eq15684 eq16
    | (have j1 := eq15684 X0 X0
       grind)
    | exact resolve eq16 eq15684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15684
  have eq16075 : ∀ X0 X1 : G, (k X0 x) = (M.op x X0) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (k X1 x) = (M.op x X1) := by
    intro X0 X1
    first
    | (have j0 := eq15955 X0 X0
       grind)
    | (have r₁ := eq15955 X0 X1
       have r₂ := eq68 x
       grind)
    | exact resolve eq15955 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15955
  have eq16405 : ∀ X0 : G, (M.op x X0) ≠ (M.op x X0) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq16075 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16075
  have eq16406 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq16405 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16405
  have eq16665 : ∀ X0 : G, x = (τ (M.op (σ x) (σ y))) ∨ (τ (k X0 (σ x))) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq22 X0 x
       have i₂ := eq16406 (τ X0)
       grind)
    | exact superpose eq16406 eq22
    | exact resolve eq22 eq16406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16406
  have eq17192 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (τ (k X0 (σ x))) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ x) (σ y))
       have i₂ := eq16665 X0
       grind)
    | exact superpose eq16665 eq10
    | (have j1 := eq16665 X0
       grind)
    | exact resolve eq10 eq16665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16665
  have eq18748 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (τ (k X0 (σ x))) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq17192 X0
       grind)
    | exact superpose eq17192 eq16
    | (have j1 := eq17192 X0
       grind)
    | exact resolve eq16 eq17192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17192
  have eq96818 : ∀ X0 X1 X2 : G, (σ (k X0 (τ (σ X1)))) = (σ (M.op X1 (τ (σ X0)))) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4600 X0 X1 (σ X1)
       have i₂ := eq19 (σ X0) X1
       grind)
    | exact superpose eq19 eq4600
    | (have j0 := eq4600 X1 X2 X2
       grind)
    | exact resolve eq4600 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4600
  have eq96834 : ∀ X0 X1 X2 : G, (σ (k X0 (τ (σ X1)))) = (σ (M.op X1 X0)) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96818 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq96818
    | (have j0 := eq96818 X0 X1 X2
       grind)
    | exact resolve eq96818 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96818
  have eq96839 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96834 X0 X1 X2
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq96834
    | (have j0 := eq96834 X0 X1 X2
       grind)
    | exact resolve eq96834 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96834
  have eq96841 : ∀ X0 X1 X2 : G, (k X0 (τ (σ X1))) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96839 X0 X1 X2
       have i₂ := eq9 (k X0 (τ (σ X1)))
       grind)
    | exact superpose eq9 eq96839
    | (have j0 := eq96839 X0 X1 X2
       grind)
    | exact resolve eq96839 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96839
  have eq96843 : ∀ X0 X1 X2 : G, (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96841 X0 X1 X2
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq96841
    | (have j0 := eq96841 X0 X1 X2
       grind)
    | exact resolve eq96841 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96841
  have eq96845 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96843 X0 X1 X2
       have i₂ := eq9 (k X0 (τ (σ X1)))
       grind)
    | exact superpose eq9 eq96843
    | (have j0 := eq96843 X0 X1 X2
       grind)
    | exact resolve eq96843 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96843
  have eq96847 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96845 X0 X1 X2
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq96845
    | (have j0 := eq96845 X0 X1 X2
       grind)
    | exact resolve eq96845 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96845
  have eq96849 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96847 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq96847
    | (have j0 := eq96847 X0 X1 X2
       grind)
    | exact resolve eq96847 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96847
  have eq97878 : ∀ X0 X1 X2 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (k X1 X0)
       have i₂ := eq96849 X1 X0 X2
       grind)
    | exact superpose eq96849 eq9
    | (have j1 := eq96849 X1 X0 X2
       grind)
    | exact resolve eq9 eq96849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96849
  have eq97894 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq97878 X0 X1 X2
       have i₂ := eq9 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq97878
    | (have j0 := eq97878 X0 X1 X1
       grind)
    | exact resolve eq97878 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97878
  have eq97987 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq97894 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97894
  have eq97988 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq97987 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97987
  have eq98010 : ∀ X0 X1 : G, (σ (M.op X1 (τ X0))) ≠ (M.op (σ X1) X0) ∨ (τ (k X0 (σ X1))) = X1 ∨ (τ X0) = (τ (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq4598 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4598
  have eq98197 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq97988 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98297 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X1) = (k (τ X0) (τ X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq98197 (τ X0) (τ X1)
       have i₂ := eq360 X1 X0
       grind)
    | exact superpose eq360 eq98197
    | (have j0 := eq98197 (τ X0) (τ X1)
       have j1 := eq360 X1 X0
       grind)
    | (have r₁ := eq98197 (τ X1) (τ X0)
       have r₂ := eq360 X0 X1
       grind)
    | exact resolve eq98197 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq98450 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X1) = (k (τ X0) (τ X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq98297 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98297
  have eq98509 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (σ (τ X1)))) ∨ (τ X1) = (k (τ X0) (τ X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq98450 X0 X1
       have i₂ := eq22 X0 (τ X1)
       grind)
    | exact superpose eq22 eq98450
    | (have j0 := eq98450 X0 X1
       grind)
    | exact resolve eq98450 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98450
  have eq98576 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ X1) = (k (τ X0) (τ X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq98509 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq98509
    | (have j0 := eq98509 X0 X1
       grind)
    | exact resolve eq98509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98509
  have eq98577 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ X1) = (k (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq98576 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98576
  have eq98620 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 (σ (τ X1)))) ∨ (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq98577 X0 X1
       have i₂ := eq22 X0 (τ X1)
       grind)
    | exact superpose eq22 eq98577
    | (have j0 := eq98577 X0 X1
       grind)
    | exact resolve eq98577 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98577
  have eq98655 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq98620 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq98620
    | (have j0 := eq98620 X0 X1
       grind)
    | exact resolve eq98620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98620
  have eq100593 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (τ X1) = (τ (k X1 X0)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq98655 X1 X0
       grind)
    | exact superpose eq98655 eq10
    | (have j1 := eq98655 X1 X0
       grind)
    | exact resolve eq10 eq98655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98655
  have eq100603 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq100593 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100593
    | (have j0 := eq100593 X0 X1
       grind)
    | exact resolve eq100593 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100593
  have eq100889 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq100603 X1 X0
       grind)
    | exact superpose eq100603 eq10
    | (have j1 := eq100603 X1 X0
       grind)
    | exact resolve eq10 eq100603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100603
  have eq100913 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq100889 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100889
    | (have j0 := eq100889 X0 X1
       grind)
    | exact resolve eq100889 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100889
  have eq101014 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (σ (M.op (τ X0) (τ X1))) = X1 ∨ (σ (M.op (τ X0) (τ X1))) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97988 X0 X1
       have i₂ := eq100913 X0 X1
       grind)
    | exact superpose eq100913 eq97988
    | (have j0 := eq97988 X1 X0
       have j1 := eq100913 X1 X0
       grind)
    | exact resolve eq97988 eq100913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97988
  have eq101118 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X0))) ≠ X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq100913 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101119 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X0))) ≠ X0 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq100913 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100913
  have eq101179 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (σ (M.op (τ X0) (τ X1))) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq101014 X0 X1
       have j1 := eq101119 X1 X0
       grind)
    | (have r₁ := eq101014 X1 X0
       have r₂ := eq101119 X0 X1
       grind)
    | (have r₁ := eq101014 X0 X0
       have r₂ := eq101119 X0 X0
       grind)
    | exact resolve eq101014 eq101119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101014
  have eq101221 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq101179 X0 X1
       have j1 := eq101118 X1 X0
       grind)
    | (have r₁ := eq101179 X1 X0
       have r₂ := eq101118 X0 X1
       grind)
    | exact resolve eq101179 eq101118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101179
  have eq101276 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 (τ X1))) ∨ (σ X0) = (k X1 (σ X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101118 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq101118
    | (have j0 := eq101118 X1 (σ X0)
       grind)
    | exact resolve eq101118 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101118
  have eq101401 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) ≠ X1 ∨ (σ X0) = (k X1 (σ X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101119 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq101119
    | (have j0 := eq101119 X1 (σ X0)
       grind)
    | exact resolve eq101119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101119
  have eq101526 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ X0)) ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101221 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq101221
    | (have j0 := eq101221 (σ X0) X1
       grind)
    | exact resolve eq101221 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101221
  have eq101803 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101401 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq101401
    | (have j0 := eq101401 X1 (σ X0)
       grind)
    | exact resolve eq101401 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101401
  have eq101839 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 (τ (σ X1)))) ∨ (σ X0) ≠ (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101803 X0 X1
       have i₂ := eq19 (σ X1) X0
       grind)
    | exact superpose eq19 eq101803
    | (have j0 := eq101803 X0 X1
       grind)
    | exact resolve eq101803 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101803
  have eq101845 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101839 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq101839
    | (have j0 := eq101839 X0 X1
       grind)
    | exact resolve eq101839 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101839
  have eq101849 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (τ (σ X1)))) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) ≠ (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq101845 X0 X1
       have i₂ := eq19 (σ X1) X0
       grind)
    | exact superpose eq19 eq101845
    | (have j0 := eq101845 X0 X1
       grind)
    | exact resolve eq101845 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101845
  have eq101850 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101849 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq101849
    | (have j0 := eq101849 X0 X1
       grind)
    | exact resolve eq101849 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101849
  have eq101863 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X1 X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101276 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq101276
    | (have j0 := eq101276 X1 (σ X0)
       grind)
    | exact resolve eq101276 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101276
  have eq101894 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 (τ (σ X1)))) ∨ (σ X1) ≠ (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101863 X0 X1
       have i₂ := eq19 (σ X1) X0
       grind)
    | exact superpose eq19 eq101863
    | (have j0 := eq101863 X0 X1
       grind)
    | exact resolve eq101863 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101863
  have eq101899 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X1) ≠ (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101894 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq101894
    | (have j0 := eq101894 X0 X1
       grind)
    | exact resolve eq101894 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101894
  have eq101902 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (τ (σ X1)))) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) ≠ (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq101899 X0 X1
       have i₂ := eq19 (σ X1) X0
       grind)
    | exact superpose eq19 eq101899
    | (have j0 := eq101899 X0 X1
       grind)
    | exact resolve eq101899 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101899
  have eq101904 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101902 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq101902
    | (have j0 := eq101902 X0 X1
       grind)
    | exact resolve eq101902 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101902
  have eq101955 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq101850 y x
       have i₂ := eq4645
       grind)
    | exact superpose eq4645 eq101850
    | (have j0 := eq101850 y x
       grind)
    | exact resolve eq101850 eq4645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4645 eq101850
  have eq102068 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq101955
  have eq102930 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq98197 (σ y) (σ x)
       have i₂ := eq102068
       grind)
    | exact superpose eq102068 eq98197
    | (have j0 := eq98197 (σ y) (σ x)
       grind)
    | (have r₁ := eq98197 (σ y) (σ x)
       have r₂ := eq102068
       grind)
    | exact resolve eq98197 eq102068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98197 eq102068
  have eq102935 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq102930
  have eq102948 : (σ y) = (σ (k y (τ (σ x)))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq102935
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq102935
    | exact resolve eq102935 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102935
  have eq102961 : (σ y) = (σ (k y x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq102948
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq102948
    | exact resolve eq102948 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102948
  have eq102962 : (σ y) = (σ (k y x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq102961
  have eq102973 : (σ x) = (σ (k y (τ (σ x)))) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq102962
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq102962
    | exact resolve eq102962 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102962
  have eq102981 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq102973
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq102973
    | exact resolve eq102973 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102973
  have eq102982 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq102981
  have eq103045 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102982
       have i₂ := eq120 x y
       grind)
    | exact superpose eq120 eq102982
    | (have j1 := eq120 x y
       grind)
    | exact resolve eq102982 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq103047 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102982
       have i₂ := eq2465 x y
       grind)
    | exact superpose eq2465 eq102982
    | (have j1 := eq2465 x y
       grind)
    | exact resolve eq102982 eq2465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2465
  have eq103063 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq102982
       grind)
    | exact superpose eq102982 eq9
    | exact resolve eq9 eq102982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102982
  have eq103086 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by grind
  clear eq103047
  have eq103087 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq103045
  have eq103121 : (σ x) = (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq103063
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq103063
    | exact resolve eq103063 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103063
  have eq103221 : (τ (σ x)) = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq9 (k y x)
       have i₂ := eq103121
       grind)
    | exact superpose eq103121 eq9
    | exact resolve eq9 eq103121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103121
  have eq103259 : y = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq103221
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq103221
    | exact resolve eq103221 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103221
  have eq103284 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq103259
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq103259
    | (have j1 := eq58 x y
       grind)
    | exact resolve eq103259 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq103288 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq103259
       have i₂ := eq1981 x y
       grind)
    | exact superpose eq1981 eq103259
    | (have j1 := eq1981 x y
       grind)
    | exact resolve eq103259 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981
  have eq103343 : y = (M.op x y) ∨ x = (M.op x y) ∨ (τ (k y x)) = (τ y) := by grind
  clear eq103288
  have eq103344 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by grind
  clear eq103284
  have eq103585 : x ≠ y ∨ x = (M.op x y) ∨ y = (k y x) := by grind
  have eq105951 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq103086
       grind)
    | exact superpose eq103086 eq16
    | exact resolve eq16 eq103086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103086
  have eq106179 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq105951
       have i₂ := eq103344
       grind)
    | exact superpose eq103344 eq105951
    | exact resolve eq105951 eq103344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105951
  have eq106195 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq106179
  have eq106196 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq106195
  have eq106296 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq106196
       grind)
    | exact superpose eq106196 eq16
    | exact resolve eq16 eq106196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106358 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq106196
       grind)
    | exact superpose eq106196 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq106196
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq106196
       grind)
    | exact resolve eq13 eq106196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106196
  have eq106372 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq106358
  have eq106390 : (σ y) = (σ (k y (τ (σ x)))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106372
       have i₂ := eq19 (σ x) y
       grind)
    | exact superpose eq19 eq106372
    | exact resolve eq106372 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106372
  have eq106442 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106390
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq106390
    | exact resolve eq106390 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106390
  have eq106464 : (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106442
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq106442
    | exact resolve eq106442 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106442
  have eq106558 : (σ x) ≠ (σ y) ∨ y = (k y x) ∨ x = y ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq106296
       have i₂ := eq103344
       grind)
    | exact superpose eq103344 eq106296
    | exact resolve eq106296 eq103344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103344 eq106296
  have eq106576 : (σ x) ≠ (σ y) ∨ y = (k y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq106558
  have eq106596 : (σ x) ≠ (σ y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq106576
       have r₂ := eq103585
       grind)
    | exact resolve eq106576 eq103585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103585 eq106576
  have eq106650 : (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq106464
       have r₂ := eq106596
       grind)
    | exact resolve eq106464 eq106596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106464
  have eq109174 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 (τ (σ X1)))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) ∨ (σ X0) = (σ (k X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq101526 X0 (σ X1)
       have i₂ := eq19 (σ X0) X1
       grind)
    | exact superpose eq19 eq101526
    | (have j0 := eq101526 X1 (σ X0)
       grind)
    | exact resolve eq101526 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101526
  have eq109281 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) ∨ (σ X0) = (σ (k X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq109174 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq109174
    | (have j0 := eq109174 X0 X1
       grind)
    | exact resolve eq109174 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109174
  have eq109310 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ (k X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq109281 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq109281
    | (have j0 := eq109281 X0 X1
       grind)
    | exact resolve eq109281 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109281
  have eq109318 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq109310 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq109310
    | (have j0 := eq109310 X0 X1
       grind)
    | exact resolve eq109310 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109310
  have eq120558 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X0)
       have i₂ := eq109318 X1 X0
       grind)
    | exact superpose eq109318 eq9
    | (have j1 := eq109318 X1 X0
       grind)
    | exact resolve eq9 eq109318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109318
  have eq120569 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq120558 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq120558
    | (have j0 := eq120558 X0 X1
       grind)
    | exact resolve eq120558 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120558
  have eq121041 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq120569 X1 X0
       grind)
    | exact superpose eq120569 eq9
    | (have j1 := eq120569 X1 X0
       grind)
    | exact resolve eq9 eq120569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120569
  have eq121066 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq121041 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq121041
    | (have j0 := eq121041 X0 X1
       grind)
    | exact resolve eq121041 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121041
  have eq121104 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = X1 ∨ (σ (M.op X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) ∨ (τ X0) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq121066 (τ X0) X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq121066
    | (have j0 := eq121066 (τ X0) X1
       grind)
    | exact resolve eq121066 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121066
  have eq121262 : ∀ X0 X1 : G, (σ (M.op X1 (τ X0))) = (M.op (σ X1) X0) ∨ (τ (k X0 (σ X1))) = X1 ∨ (τ X0) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq121104 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq121104
    | (have j0 := eq121104 X0 X1
       grind)
    | exact resolve eq121104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121104
  have eq121277 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (τ X0) = (τ (k X0 (σ X1))) ∨ (τ (k X0 (σ X1))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq98010 X0 X1
       have j1 := eq121262 X0 X1
       grind)
    | (have r₁ := eq98010 X0 X1
       have r₂ := eq121262 X0 X1
       grind)
    | exact resolve eq98010 eq121262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98010 eq121262
  have eq122189 : ∀ X0 X1 : G, (σ (k X0 (τ (σ X1)))) = (M.op (σ X1) (σ X0)) ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq121277 (σ X1) X1
       have i₂ := eq19 (σ X1) X1
       grind)
    | exact superpose eq19 eq121277
    | exact resolve eq121277 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq121277
  have eq122209 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (τ (σ X0)) = (τ (σ (k X0 (τ (σ X1))))) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq122189 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq122189
    | (have j0 := eq122189 X0 X1
       grind)
    | exact resolve eq122189 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122189
  have eq122213 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq122209 X0 X1
       have i₂ := eq9 (k X0 (τ (σ X1)))
       grind)
    | exact superpose eq9 eq122209
    | (have j0 := eq122209 X0 X1
       grind)
    | exact resolve eq122209 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122209
  have eq122216 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq122213 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq122213
    | (have j0 := eq122213 X0 X1
       grind)
    | exact resolve eq122213 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122213
  have eq122218 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (τ (σ (k X0 (τ (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq122216 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq122216
    | (have j0 := eq122216 X0 X1
       grind)
    | exact resolve eq122216 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122216
  have eq122220 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = X1 ∨ (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq122218 X0 X1
       have i₂ := eq9 (k X0 (τ (σ X1)))
       grind)
    | exact superpose eq9 eq122218
    | (have j0 := eq122218 X0 X1
       grind)
    | exact resolve eq122218 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122218
  have eq122222 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq122220 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq122220
    | (have j0 := eq122220 X0 X1
       grind)
    | exact resolve eq122220 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122220
  have eq122327 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X0)
       have i₂ := eq122222 X1 X0
       grind)
    | exact superpose eq122222 eq9
    | (have j1 := eq122222 X1 X0
       grind)
    | exact resolve eq9 eq122222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122222
  have eq122479 : ∀ X0 X1 : G, (τ (M.op (σ X1) (σ X0))) ≠ X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq122327 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122480 : ∀ X0 X1 : G, (τ (M.op (σ X1) (σ X0))) ≠ X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq122327 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122327
  have eq122523 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) ≠ X1 ∨ (k X1 (τ X0)) = X1 ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq122479 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq122479
    | (have j0 := eq122479 X1 (τ X0)
       grind)
    | exact resolve eq122479 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122479
  have eq122669 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 (σ X1))) ∨ (k X1 (τ X0)) = X1 ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq122480 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq122480
    | (have j0 := eq122480 X1 (τ X0)
       grind)
    | exact resolve eq122480 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122480
  have eq122838 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X1 X0)) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X1) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq122523 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq122523
    | (have j0 := eq122523 X1 (τ X0)
       grind)
    | exact resolve eq122523 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122523
  have eq122953 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (σ (τ X1)))) ∨ (τ X0) ≠ (τ (M.op X1 X0)) ∨ (τ X1) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq122838 X0 X1
       have i₂ := eq22 X0 (τ X1)
       grind)
    | exact superpose eq22 eq122838
    | (have j0 := eq122838 X0 X1
       grind)
    | exact resolve eq122838 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122838
  have eq123001 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ X0) ≠ (τ (M.op X1 X0)) ∨ (τ X1) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq122953 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq122953
    | (have j0 := eq122953 X0 X1
       grind)
    | exact resolve eq122953 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122953
  have eq123018 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 (σ (τ X1)))) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ X0) ≠ (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq123001 X0 X1
       have i₂ := eq22 X0 (τ X1)
       grind)
    | exact superpose eq22 eq123001
    | (have j0 := eq123001 X0 X1
       grind)
    | exact resolve eq123001 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123001
  have eq123020 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123018 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq123018
    | (have j0 := eq123018 X0 X1
       grind)
    | exact resolve eq123018 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123018
  have eq123247 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X0)) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X1) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq122669 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq122669
    | (have j0 := eq122669 X1 (τ X0)
       grind)
    | exact resolve eq122669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122669
  have eq123350 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 (σ (τ X1)))) ∨ (τ X1) ≠ (τ (M.op X1 X0)) ∨ (τ X1) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123247 X0 X1
       have i₂ := eq22 X0 (τ X1)
       grind)
    | exact superpose eq22 eq123247
    | (have j0 := eq123247 X0 X1
       grind)
    | exact resolve eq123247 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123247
  have eq123387 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ X1) ≠ (τ (M.op X1 X0)) ∨ (τ X1) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq123350 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq123350
    | (have j0 := eq123350 X0 X1
       grind)
    | exact resolve eq123350 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123350
  have eq123413 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 (σ (τ X1)))) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ X1) ≠ (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq123387 X0 X1
       have i₂ := eq22 X0 (τ X1)
       grind)
    | exact superpose eq22 eq123387
    | (have j0 := eq123387 X0 X1
       grind)
    | exact resolve eq123387 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123387
  have eq123419 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ X1) ≠ (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq123413 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq123413
    | (have j0 := eq123413 X0 X1
       grind)
    | exact resolve eq123413 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123413
  have eq123476 : (τ y) ≠ (τ y) ∨ (τ (k y x)) = (τ y) ∨ (τ (k y x)) = (τ x) ∨ x = (M.op x y) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq123020 y x
       have i₂ := eq103343
       grind)
    | exact superpose eq103343 eq123020
    | (have j0 := eq123020 y x
       grind)
    | exact resolve eq123020 eq103343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103343
  have eq123524 : (τ y) ≠ (τ y) ∨ (τ (k y x)) = (τ y) ∨ (τ (k y x)) = (τ x) ∨ x = (M.op x y) := by grind
  clear eq123476
  have eq123525 : x = (M.op x y) ∨ (τ (k y x)) = (τ x) ∨ (τ (k y x)) = (τ y) := by grind
  clear eq123524
  have eq123732 : x ≠ x ∨ x = (k y x) ∨ (τ (k y x)) = (τ x) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq8202
       have i₂ := eq123525
       grind)
    | exact superpose eq123525 eq8202
    | (have r₁ := eq8202
       have r₂ := eq123525
       grind)
    | exact resolve eq8202 eq123525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8202
  have eq123816 : (τ x) ≠ (τ y) ∨ (τ (k y x)) = (τ y) ∨ (τ (k y x)) = (τ x) ∨ (τ (k y x)) = (τ x) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq123020 y x
       have i₂ := eq123525
       grind)
    | exact superpose eq123525 eq123020
    | (have j0 := eq123020 y x
       grind)
    | exact resolve eq123020 eq123525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123525
  have eq123817 : (τ x) ≠ (τ y) ∨ (τ (k y x)) = (τ y) ∨ (τ (k y x)) = (τ x) := by grind
  clear eq123816
  have eq123852 : x = (k y x) ∨ (τ (k y x)) = (τ x) ∨ (τ (k y x)) = (τ y) := by grind
  clear eq123732
  have eq123946 : (τ (M.op x y)) = (τ x) ∨ y = (M.op x y) ∨ (τ x) = (τ y) ∨ (τ (k y x)) = (τ x) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq1778 x y
       have i₂ := eq123852
       grind)
    | exact superpose eq123852 eq1778
    | (have j0 := eq1778 x y
       grind)
    | exact resolve eq1778 eq123852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1778 eq123852
  have eq123961 : (τ (M.op x y)) = (τ x) ∨ y = (M.op x y) ∨ (τ (k y x)) = (τ x) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have r₁ := eq123946
       have r₂ := eq123817
       grind)
    | exact resolve eq123946 eq123817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123817 eq123946
  have eq123970 : y = (M.op x y) ∨ (τ (k y x)) = (τ x) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have j1 := eq123419 y x
       grind)
    | (have r₁ := eq123961
       have r₂ := eq123419 y x
       grind)
    | exact resolve eq123961 eq123419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123419 eq123961
  have eq124048 : (τ y) ≠ (τ y) ∨ (τ (k y x)) = (τ y) ∨ (τ (k y x)) = (τ x) ∨ (τ (k y x)) = (τ x) ∨ (τ (k y x)) = (τ y) := by
    first
    | (have i₁ := eq123020 y x
       have i₂ := eq123970
       grind)
    | exact superpose eq123970 eq123020
    | (have j0 := eq123020 y x
       grind)
    | exact resolve eq123020 eq123970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123970
  have eq124049 : (τ y) ≠ (τ y) ∨ (τ (k y x)) = (τ y) ∨ (τ (k y x)) = (τ x) := by grind
  clear eq124048
  have eq124050 : (τ (k y x)) = (τ y) ∨ (τ (k y x)) = (τ x) := by grind
  clear eq124049
  have eq124119 : (k y x) = (σ (τ y)) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq124050
       grind)
    | exact superpose eq124050 eq10
    | exact resolve eq10 eq124050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124175 : (τ x) ≠ (τ y) ∨ (τ (k y x)) = (τ x) := by grind
  clear eq124050
  have eq124188 : y = (k y x) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq124119
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq124119
    | exact resolve eq124119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124119
  have eq124239 : ∀ X0 : G, x = y ∨ (k X0 x) = (M.op x X0) ∨ (τ (k y x)) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq8045 X0
       have i₂ := eq124188
       grind)
    | exact superpose eq124188 eq8045
    | (have j0 := eq8045 X0
       grind)
    | exact resolve eq8045 eq124188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8045
  have eq124308 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k X0 x) = (M.op x X0) ∨ (τ (k y x)) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq124239 X0
       grind)
    | exact superpose eq124239 eq16
    | (have j1 := eq124239 X0
       grind)
    | exact resolve eq16 eq124239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124239
  have eq124877 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (τ (k y x)) = (τ x) := by
    intro X0
    first
    | (have j0 := eq124308 X0
       grind)
    | (have r₁ := eq124308 X0
       have r₂ := eq68 x
       grind)
    | exact resolve eq124308 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124308
  have eq125111 : y = (M.op x y) ∨ (τ x) = (τ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq124877 y
       have i₂ := eq103259
       grind)
    | exact superpose eq103259 eq124877
    | exact resolve eq124877 eq103259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103259
  have eq125247 : ∀ X0 : G, (τ (k X0 (σ x))) = (M.op x (τ X0)) ∨ (τ (k y x)) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq22 X0 x
       have i₂ := eq124877 (τ X0)
       grind)
    | exact superpose eq124877 eq22
    | exact resolve eq22 eq124877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq124877
  have eq125475 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x x) ∨ (τ x) = (τ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq125111
       grind)
    | exact superpose eq125111 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq125111
       grind)
    | exact resolve eq12 eq125111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125111
  have eq125494 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x x) ∨ (τ x) = (τ y) := by grind
  clear eq125475
  have eq125495 : x = (M.op x x) ∨ x = (k y x) ∨ (τ x) = (τ y) := by grind
  clear eq125494
  have eq125573 : (τ x) ≠ (τ x) ∨ (τ x) = (τ (k x x)) ∨ (τ x) = (τ (k x x)) ∨ x = (k y x) ∨ (τ x) = (τ y) := by
    first
    | (have i₁ := eq123020 x x
       have i₂ := eq125495
       grind)
    | exact superpose eq125495 eq123020
    | (have j0 := eq123020 x x
       grind)
    | exact resolve eq123020 eq125495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125495
  have eq125574 : (τ x) ≠ (τ x) ∨ (τ x) = (τ (k x x)) ∨ x = (k y x) ∨ (τ x) = (τ y) := by grind
  clear eq125573
  have eq125575 : (τ x) = (τ (k x x)) ∨ x = (k y x) ∨ (τ x) = (τ y) := by grind
  clear eq125574
  have eq125607 : x = (k y x) ∨ (τ x) = (τ (M.op x x)) ∨ (τ x) = (τ y) := by
    first
    | (have i₁ := eq125575
       have i₂ := eq46 x
       grind)
    | exact superpose eq46 eq125575
    | exact resolve eq125575 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125575
  have eq126102 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op x (τ X0))) ∨ (τ (k y x)) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (σ x))
       have i₂ := eq125247 X0
       grind)
    | exact superpose eq125247 eq10
    | exact resolve eq10 eq125247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125247
  have eq127125 : x = y ∨ (τ x) = (τ (M.op x x)) ∨ (τ x) = (τ y) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq125607
       have i₂ := eq124188
       grind)
    | exact superpose eq124188 eq125607
    | exact resolve eq125607 eq124188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124188 eq125607
  have eq127213 : x = y ∨ (τ x) = (τ (M.op x x)) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have r₁ := eq127125
       have r₂ := eq124175
       grind)
    | exact resolve eq127125 eq124175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127125
  have eq127740 : (τ x) ≠ (τ x) ∨ (τ x) = (τ (k x x)) ∨ (τ x) = (τ (M.op x x)) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq124175
       have i₂ := eq127213
       grind)
    | exact superpose eq127213 eq124175
    | exact resolve eq124175 eq127213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124175 eq127213
  have eq127759 : (τ x) = (τ (k x x)) ∨ (τ x) = (τ (M.op x x)) ∨ (τ (k y x)) = (τ x) := by grind
  clear eq127740
  have eq127863 : (τ x) = (τ (M.op x x)) ∨ (τ x) = (τ (M.op x x)) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq127759
       have i₂ := eq46 x
       grind)
    | exact superpose eq46 eq127759
    | exact resolve eq127759 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127759
  have eq127864 : (τ x) = (τ (M.op x x)) ∨ (τ (k y x)) = (τ x) := by grind
  clear eq127863
  have eq128078 : (M.op x x) = (σ (τ x)) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq127864
       grind)
    | exact superpose eq127864 eq10
    | exact resolve eq10 eq127864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127864
  have eq128140 : x = (M.op x x) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq128078
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq128078
    | exact resolve eq128078 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128078
  have eq128152 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (τ (k y x)) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq86 x X0
       have i₂ := eq128140
       grind)
    | exact superpose eq128140 eq86
    | (have j0 := eq86 x X0
       grind)
    | exact resolve eq86 eq128140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128140
  have eq128190 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (τ (k y x)) = (τ x) := by
    intro X0
    first
    | (have j0 := eq128152 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128152
  have eq128438 : ∀ X0 : G, (M.op (σ x) X0) = (σ (M.op x (τ X0))) ∨ (τ (k y x)) = (τ x) ∨ (τ (k y x)) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq126102 X0
       have i₂ := eq128190 X0
       grind)
    | exact superpose eq128190 eq126102
    | exact resolve eq126102 eq128190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126102 eq128190
  have eq128479 : ∀ X0 : G, (M.op (σ x) X0) = (σ (M.op x (τ X0))) ∨ (τ (k y x)) = (τ x) := by
    intro X0
    first
    | (have j0 := eq128438 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128438
  have eq129479 : (σ (M.op x y)) ≠ (σ (M.op x (τ (σ y)))) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq128479 (σ y)
       grind)
    | exact superpose eq128479 eq16
    | exact resolve eq16 eq128479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128479
  have eq129651 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (τ (k y x)) = (τ x) := by
    first
    | (have i₁ := eq129479
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq129479
    | exact resolve eq129479 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129479
  have eq129652 : (τ (k y x)) = (τ x) := by grind
  clear eq129651
  have eq130434 : (k y x) = (σ (τ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq129652
       grind)
    | exact superpose eq129652 eq10
    | exact resolve eq10 eq129652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129652
  have eq130521 : x = (k y x) := by
    first
    | (have i₁ := eq130434
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq130434
    | exact resolve eq130434 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130434
  have eq130675 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2735
       have i₂ := eq130521
       grind)
    | exact superpose eq130521 eq2735
    | exact resolve eq2735 eq130521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2735
  have eq132158 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103087
       have i₂ := eq130521
       grind)
    | exact superpose eq130521 eq103087
    | exact resolve eq103087 eq130521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103087
  have eq132454 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106596
       have i₂ := eq130521
       grind)
    | exact superpose eq130521 eq106596
    | exact resolve eq106596 eq130521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106596
  have eq132474 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106650
       have i₂ := eq130521
       grind)
    | exact superpose eq130521 eq106650
    | exact resolve eq106650 eq130521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106650
  have eq133791 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq132474
       have i₂ := eq130521
       grind)
    | exact superpose eq130521 eq132474
    | exact resolve eq132474 eq130521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132474
  have eq134036 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq130675
       have r₂ := eq132158
       grind)
    | exact resolve eq130675 eq132158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130675 eq132158
  have eq134108 : x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have r₁ := eq133791
       have r₂ := eq132454
       grind)
    | exact resolve eq133791 eq132454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132454 eq133791
  have eq135177 : x ≠ x ∨ y = (k y x) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq134108
       grind)
    | exact superpose eq134108 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq134108
       grind)
    | exact resolve eq13 eq134108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134108
  have eq135199 : x ≠ x ∨ y = (k y x) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq135177
  have eq135200 : y = (k y x) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq135199
  have eq135288 : x = y ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq135200
       have i₂ := eq130521
       grind)
    | exact superpose eq130521 eq135200
    | exact resolve eq135200 eq130521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135200
  have eq135289 : x = (M.op x x) ∨ x = y ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq135288
  have eq135320 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ x = y ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq101904 x x
       have i₂ := eq135289
       grind)
    | exact superpose eq135289 eq101904
    | (have j0 := eq101904 x x
       grind)
    | (have r₁ := eq101904 x x
       have r₂ := eq135289
       grind)
    | exact resolve eq101904 eq135289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101904 eq135289
  have eq135328 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x x)) ∨ x = y ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq135320
  have eq135329 : (σ x) = (σ (k x x)) ∨ x = y ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq135328
  have eq135352 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq135329
       have i₂ := eq46 x
       grind)
    | exact superpose eq46 eq135329
    | exact resolve eq135329 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135329
  have eq135353 : (σ x) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq135352
  have eq135373 : (τ (σ x)) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq135353
       grind)
    | exact superpose eq135353 eq9
    | exact resolve eq9 eq135353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135353
  have eq135423 : x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq135373
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq135373
    | exact resolve eq135373 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135373
  have eq135429 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11 X0 x
       have i₂ := eq135423
       grind)
    | exact superpose eq135423 eq11
    | (have j0 := eq11 X0 x
       grind)
    | (have r₁ := eq11 X0 x
       have r₂ := eq135423
       grind)
    | exact resolve eq11 eq135423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135446 : (τ x) ≠ (τ x) ∨ (τ x) = (τ (k x x)) ∨ (τ x) = (τ (k x x)) ∨ x = y := by
    first
    | (have i₁ := eq123020 x x
       have i₂ := eq135423
       grind)
    | exact superpose eq135423 eq123020
    | (have j0 := eq123020 x x
       grind)
    | exact resolve eq123020 eq135423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123020 eq135423
  have eq135447 : (τ x) ≠ (τ x) ∨ (τ x) = (τ (k x x)) ∨ x = y := by grind
  clear eq135446
  have eq135448 : (τ x) = (τ (k x x)) ∨ x = y := by grind
  clear eq135447
  have eq135471 : ∀ X0 : G, x = y ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq135429 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135429
  have eq135472 : x = y ∨ (τ x) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq135448
       have i₂ := eq46 x
       grind)
    | exact superpose eq46 eq135448
    | exact resolve eq135448 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq135448
  have eq135487 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq135471 X0
       grind)
    | exact superpose eq135471 eq16
    | (have j1 := eq135471 X0
       grind)
    | exact resolve eq16 eq135471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135471
  have eq135711 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq135487 X0
       grind)
    | (have r₁ := eq135487 X0
       have r₂ := eq68 x
       grind)
    | exact resolve eq135487 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq135487
  have eq138254 : x = (M.op x y) := by
    first
    | (have i₁ := eq130521
       have i₂ := eq135711 y
       grind)
    | exact superpose eq135711 eq130521
    | exact resolve eq130521 eq135711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130521 eq135711
  have eq138383 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq138254
       grind)
    | exact superpose eq138254 eq16
    | exact resolve eq16 eq138254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138425 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (τ (k X0 (σ x))) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18748 X0
       have i₂ := eq138254
       grind)
    | exact superpose eq138254 eq18748
    | (have j0 := eq18748 X0
       grind)
    | exact resolve eq18748 eq138254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18748
  have eq139704 : ∀ X0 : G, (τ (k X0 (σ x))) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have j0 := eq138425 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138425
  have eq144244 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq134036
       have r₂ := eq138383
       grind)
    | exact resolve eq134036 eq138383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134036
  have eq148310 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq138383
       have i₂ := eq144244
       grind)
    | exact superpose eq144244 eq138383
    | exact resolve eq138383 eq144244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138383
  have eq160730 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op x (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (σ x))
       have i₂ := eq139704 X0
       grind)
    | exact superpose eq139704 eq10
    | exact resolve eq10 eq139704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139704
  have eq162622 : (σ x) ≠ (σ x) ∨ (τ x) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq148310
       have i₂ := eq135472
       grind)
    | exact superpose eq135472 eq148310
    | exact resolve eq148310 eq135472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135472
  have eq162623 : (τ x) = (τ (M.op x x)) := by grind
  clear eq162622
  have eq162649 : (M.op x x) = (σ (τ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq162623
       grind)
    | exact superpose eq162623 eq10
    | exact resolve eq10 eq162623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162623
  have eq163026 : x = (M.op x x) := by
    first
    | (have i₁ := eq162649
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq162649
    | exact resolve eq162649 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162649
  have eq166162 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq86 x X0
       have i₂ := eq163026
       grind)
    | exact superpose eq163026 eq86
    | (have j0 := eq86 x X0
       grind)
    | exact resolve eq86 eq163026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq163026
  have eq166201 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq166162 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166162
  have eq166296 : ∀ X0 : G, (M.op (σ x) X0) = (σ (M.op x (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq166201 X0
       have i₂ := eq160730 X0
       grind)
    | exact superpose eq160730 eq166201
    | exact resolve eq166201 eq160730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160730 eq166201
  have eq166759 : (σ y) = (σ (M.op x (τ (σ y)))) := by
    first
    | (have i₁ := eq144244
       have i₂ := eq166296 (σ y)
       grind)
    | exact superpose eq166296 eq144244
    | exact resolve eq144244 eq166296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144244 eq166296
  have eq166877 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq166759
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq166759
    | exact resolve eq166759 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166759
  have eq167245 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq166877
       have i₂ := eq138254
       grind)
    | exact superpose eq138254 eq166877
    | exact resolve eq166877 eq138254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138254 eq166877
  have eq167475 : False := by grind
  exact eq167475

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then X else if m(Y,X) = X then Y
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_pyx_y_pyx_x_pyx_x_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
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
  have eq59 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (k y x) := by
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
  have eq60 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq67 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq70 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
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
  have eq71 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq16
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq11 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq87
    | (have j0 := eq87 (σ X0) (σ X1)
       grind)
    | exact resolve eq87 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq87
    | (have j0 := eq87 (σ x) (σ X0)
       grind)
    | exact resolve eq87 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq93 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq87
    | (have j0 := eq87 (σ y) (σ X0)
       grind)
    | exact resolve eq87 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq87 y x
       grind)
    | exact superpose eq87 eq67
    | (have j1 := eq87 y x
       grind)
    | exact resolve eq67 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq118 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq120 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
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
  have eq127 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq87 sF1 (σ X0)
       grind)
    | exact superpose eq87 eq37
    | (have j1 := eq87 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq127 eq16
    | exact resolve eq16 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq87 (σ X0) sF2
       grind)
    | exact superpose eq87 eq39
    | (have j1 := eq87 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq87 sF0 sF0
       grind)
    | exact superpose eq87 eq129
    | (have j1 := eq87 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq129 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq160
  have eq222 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
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
  have eq268 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq16
    | exact resolve eq16 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq291 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq120 eq16
    | exact resolve eq16 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq571 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq119 eq87
    | (have j0 := eq87 (σ y) (σ x)
       grind)
    | exact resolve eq87 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq571
    | exact resolve eq571 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq575 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq572
       have r₂ := eq27
       grind)
    | exact resolve eq572 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq577 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq575
    | exact resolve eq575 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq579 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq577
    | exact resolve eq577 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq581 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq579 eq71
    | (have r₁ := eq71
       have r₂ := eq579
       grind)
    | exact resolve eq71 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq584 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq579
  have eq585 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq581
  have eq623 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq91 X0 X0
       grind)
    | exact superpose eq91 eq14
    | (have j0 := eq14 X1 (σ X0)
       have j1 := eq91 X0 X0
       grind)
    | (have r₁ := eq14 X0 (σ X0)
       have r₂ := eq91 X0 X0
       grind)
    | exact resolve eq14 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq628 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq623 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq631 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq628 X0 X1
       have j1 := eq14 X1 (σ X0)
       grind)
    | (have r₁ := eq628 X0 X1
       have r₂ := eq14 X0 (σ X0)
       grind)
    | exact resolve eq628 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq649 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq585
       have r₂ := eq584
       grind)
    | exact resolve eq585 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq585
  have eq652 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq649 eq119
    | exact resolve eq119 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq656 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq652
  have eq666 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq656 eq14
    | (have j0 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq656
       grind)
    | exact resolve eq14 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq667 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq666 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq719 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq667 eq119
    | exact resolve eq119 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq724 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq719
  have eq730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq724
    | exact resolve eq724 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq732 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq730
       have r₂ := eq27
       grind)
    | exact resolve eq730 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq778 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq732 eq60
    | (have r₁ := eq60
       have r₂ := eq732
       grind)
    | exact resolve eq60 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq780 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq778
  have eq830 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq780 eq119
    | exact resolve eq119 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq836 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq830
  have eq847 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq836 eq14
    | (have j0 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq836
       grind)
    | exact resolve eq14 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq848 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq847 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq906 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq848 eq119
    | exact resolve eq119 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq848
  have eq914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq906
  have eq922 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq914
    | exact resolve eq914 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq924 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq922
       have r₂ := eq27
       grind)
    | exact resolve eq922 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq927 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq924 eq29
    | exact resolve eq29 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq955 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq30 eq927
    | exact resolve eq927 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq956 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq955
  have eq1005 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq956 eq28
    | exact resolve eq28 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq1028 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq1005
    | exact resolve eq1005 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1029 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1028
  have eq1030 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1029 eq20
    | exact resolve eq20 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1034 : y ≠ y ∨ x = y ∨ x = (M.op x x) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1029 eq70
    | (have r₁ := eq70
       have r₂ := eq1029
       grind)
    | exact resolve eq70 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1036 : (σ (k y x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1029 eq127
    | exact resolve eq127 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq1040 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1029 eq291
    | exact resolve eq291 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq1042 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq1029
  have eq1043 : x = y ∨ x = (M.op x x) ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq1034
  have eq1045 : ∀ X0 : G, (τ (k (σ y) X0)) = (τ (k (σ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1040 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq1040
    | exact resolve eq1040 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq1040
  have eq1049 : (k (σ y) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1036
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq1036
    | exact resolve eq1036 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1054 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1030
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1030
    | exact resolve eq1030 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1106 : ∀ X0 : G, (σ (k y X0)) = (k (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1054 eq36
    | exact resolve eq36 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1133 : ∀ X0 : G, (σ (k y X0)) = (σ (k (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37 eq1106
    | exact resolve eq1106 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1106
  have eq1214 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1049 eq87
    | (have j0 := eq87 (σ y) (σ x)
       grind)
    | exact resolve eq87 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1226 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1214
    | exact resolve eq1214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1229 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1226
    | exact resolve eq1226 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1231 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1229
    | exact resolve eq1229 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq2101 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq631 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq631
    | (have j0 := eq631 (τ X0) X1
       grind)
    | exact resolve eq631 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq2109 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2101 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2101
    | (have j0 := eq2101 X0 X1
       grind)
    | exact resolve eq2101 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101
  have eq2119 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2109 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2109
    | (have j0 := eq2109 X0 X1
       grind)
    | exact resolve eq2109 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2109
  have eq2158 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  clear eq92
  have eq2166 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2158
  have eq2171 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2166
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq2166
    | exact resolve eq2166 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2166
  have eq2181 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | (have r₁ := eq2171
       have r₂ := eq14 x (σ x)
       grind)
    | exact resolve eq2171 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171
  have eq2219 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq93 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2220 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq93 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq2485 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq130
    | (have j0 := eq130 (M.op x y)
       grind)
    | exact resolve eq130 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq2490 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2485
  have eq2493 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq129 eq2490
    | exact resolve eq2490 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq2490
  have eq2505 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq14 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq2493
       have r₂ := eq14 x (σ (M.op x y))
       grind)
    | exact resolve eq2493 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2493
  have eq2557 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq158 eq12
    | (have j0 := eq12 (σ X0) (σ x)
       have j1 := eq158 x
       grind)
    | (have r₁ := eq12 (σ X0) (σ x)
       have r₂ := eq158 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq158 x
       grind)
    | exact resolve eq12 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2559 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq158 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq2563 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2557 X0
       have j1 := eq12 (σ X0) (σ x)
       grind)
    | (have r₁ := eq2557 X0
       have r₂ := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq2557 X0
       have r₂ := eq12 (σ X0) (σ x)
       grind)
    | (have r₁ := eq2557 x
       have r₂ := eq12 (σ x) (σ x)
       grind)
    | exact resolve eq2557 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557
  have eq2574 : ∀ X0 : G, (σ x) = (σ (k X0 x)) ∨ (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq39 eq2563
    | (have j0 := eq2563 X0
       grind)
    | exact resolve eq2563 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq2563
  have eq2575 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ x) = (σ (k X0 x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2574 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574
  have eq9366 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1231 eq138
    | exact resolve eq138 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231
  have eq19282 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2505 eq168
    | exact resolve eq168 eq2505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq2505
  have eq191324 : (σ (k y x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9366 eq1133
    | exact resolve eq1133 eq9366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9366
  have eq191370 : (σ (k y x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq191324
  have eq191390 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq191370
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq191370
    | exact resolve eq191370 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191370
  have eq191415 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq191390
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq191390
    | exact resolve eq191390 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191390
  have eq191425 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1054 eq191415
    | exact resolve eq191415 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191415
  have eq191528 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq191425
  have eq191531 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq191528
       have r₂ := eq27
       grind)
    | exact resolve eq191528 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191528
  have eq191750 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq191531 eq138
    | exact resolve eq138 eq191531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191531
  have eq191808 : (σ (k y x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq191750 eq1133
    | exact resolve eq1133 eq191750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133 eq191750
  have eq191854 : (σ (k y x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq191808
  have eq191874 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq191854
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq191854
    | exact resolve eq191854 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191854
  have eq191899 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq191874
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq191874
    | exact resolve eq191874 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191874
  have eq342913 : x = (k y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1043
       have r₂ := eq1042
       grind)
    | exact resolve eq1043 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq342916 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq342913
       grind)
    | exact superpose eq342913 eq67
    | exact resolve eq67 eq342913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343008 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq342916
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq342916
    | exact resolve eq342916 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342916
  have eq343120 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq343008 eq191899
    | exact resolve eq191899 eq343008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191899
  have eq343130 : (τ (σ x)) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq343008 eq1045
    | exact resolve eq1045 eq343008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343185 : (τ (σ x)) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq343130
  have eq343195 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq343120
  have eq343230 : (τ (σ x)) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq138 eq343185
    | exact resolve eq343185 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343185
  have eq343244 : x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq343230
    | exact resolve eq343230 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343230
  have eq343247 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq343195
       grind)
    | exact superpose eq343195 eq14
    | (have j0 := eq14 X0 x
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq343195
       grind)
    | exact resolve eq14 eq343195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343195
  have eq343248 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq343247 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343247
  have eq343731 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2219 x
       have i₂ := eq343248 y
       grind)
    | exact superpose eq343248 eq2219
    | (have j0 := eq2219 x
       grind)
    | exact resolve eq2219 eq343248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219 eq343248
  have eq344324 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq343731
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq343731
    | exact resolve eq343731 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343731
  have eq344402 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq344324
    | exact resolve eq344324 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344324
  have eq344455 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq344402
       have r₂ := eq1054
       grind)
    | exact resolve eq344402 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344402
  have eq344469 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq344455
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq344455
    | exact resolve eq344455 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344455
  have eq344476 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq344469
    | exact resolve eq344469 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344469
  have eq344481 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq344476
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq344476
    | exact resolve eq344476 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344476
  have eq344487 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq344481
    | exact resolve eq344481 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344481
  have eq344488 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq344487
  have eq344492 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq344488 eq27
    | exact resolve eq27 eq344488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344488
  have eq344503 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq344492
       have r₂ := eq1054
       grind)
    | exact resolve eq344492 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054 eq344492
  have eq344508 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq344503 eq60
    | (have r₁ := eq60
       have r₂ := eq344503
       grind)
    | exact resolve eq60 eq344503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq344503
  have eq344509 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq344508
  have eq344536 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq344509 eq76
    | exact resolve eq76 eq344509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344565 : (τ (σ y)) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq344509 eq1045
    | exact resolve eq1045 eq344509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045 eq344509
  have eq344621 : (τ (σ y)) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq344565
  have eq344669 : (τ (σ y)) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq138 eq344621
    | exact resolve eq344621 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq344621
  have eq344673 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq344536
    | exact resolve eq344536 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344536
  have eq344685 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (k (M.op x y) x) := by
    first
    | exact superpose eq29 eq344669
    | exact resolve eq344669 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq344669
  have eq344819 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (k y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq344673 eq14
    | (have j0 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq344673
       grind)
    | exact resolve eq14 eq344673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344673
  have eq344820 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (k y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq344819 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344819
  have eq349538 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq344820 eq76
    | exact resolve eq76 eq344820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq349566 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq344820 eq343008
    | exact resolve eq343008 eq344820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343008 eq344820
  have eq349930 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (k y x) := by grind
  clear eq349566
  have eq350109 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | (have r₁ := eq349930
       have r₂ := eq59
       grind)
    | exact resolve eq349930 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349930
  have eq350118 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq349538
    | exact resolve eq349538 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349538
  have eq350131 : y = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq350109
    | exact resolve eq350109 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350109
  have eq350241 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2559 y
       have i₂ := eq350131
       grind)
    | exact superpose eq350131 eq2559
    | (have j0 := eq2559 y
       grind)
    | exact resolve eq2559 eq350131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2559 eq350131
  have eq350276 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq350241
  have eq350308 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq350276
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq350276
    | exact resolve eq350276 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350276
  have eq350344 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq350308
    | exact resolve eq350308 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350308
  have eq350366 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq350344
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq350344
    | exact resolve eq350344 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350344
  have eq350381 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq350366
    | exact resolve eq350366 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350366
  have eq350382 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq350381
  have eq350410 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq350382
       grind)
    | exact superpose eq350382 eq14
    | (have j0 := eq14 X0 x
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq350382
       grind)
    | exact resolve eq14 eq350382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350382
  have eq350411 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq350410 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350410
  have eq350730 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2220 x
       have i₂ := eq350411 y
       grind)
    | exact superpose eq350411 eq2220
    | (have j0 := eq2220 x
       grind)
    | exact resolve eq2220 eq350411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220 eq350411
  have eq351216 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq350730
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq350730
    | exact resolve eq350730 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350730
  have eq351287 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq351216
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq351216
    | exact resolve eq351216 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351216
  have eq351340 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq351287
    | exact resolve eq351287 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351287
  have eq351354 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq351340
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq351340
    | exact resolve eq351340 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351340
  have eq351362 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq351354
    | exact resolve eq351354 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351354
  have eq351363 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq351362
  have eq351369 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq351363
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq351363
    | exact resolve eq351363 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351363
  have eq351376 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq351369
    | exact resolve eq351369 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351369
  have eq351377 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq351376
  have eq351544 : x = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq350118
       have i₂ := eq342913
       grind)
    | exact superpose eq342913 eq350118
    | exact resolve eq350118 eq342913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342913 eq350118
  have eq351603 : x = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq351544
  have eq351646 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq351603
       have r₂ := eq1042
       grind)
    | exact resolve eq351603 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351603
  have eq351763 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq351646
       grind)
    | exact superpose eq351646 eq14
    | (have j0 := eq14 X0 x
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq351646
       grind)
    | exact resolve eq14 eq351646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351764 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq351763 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351763
  have eq352442 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq43
       have i₂ := eq351764 x
       grind)
    | exact superpose eq351764 eq43
    | exact resolve eq43 eq351764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352455 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq67
       have i₂ := eq351764 y
       grind)
    | exact superpose eq351764 eq67
    | exact resolve eq67 eq351764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351764
  have eq353151 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq352455
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq352455
    | exact resolve eq352455 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352455
  have eq353152 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2181 eq352442
    | exact resolve eq352442 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352442
  have eq353224 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq353151
    | exact resolve eq353151 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353151
  have eq370892 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq353152
       have i₂ := eq351646
       grind)
    | exact superpose eq351646 eq353152
    | exact resolve eq353152 eq351646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351646 eq353152
  have eq371080 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq370892
  have eq371084 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq371080
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq371080
    | exact resolve eq371080 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371080
  have eq371091 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq371084 eq14
    | (have j0 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq371084
       grind)
    | exact resolve eq14 eq371084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371084
  have eq371092 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq371091 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371091
  have eq371300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq371092 eq353224
    | exact resolve eq353224 eq371092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353224 eq371092
  have eq371673 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq371300
  have eq371894 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq371673
    | exact resolve eq371673 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371673
  have eq371917 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq371894
       have r₂ := eq27
       grind)
    | exact resolve eq371894 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371894
  have eq371936 : (σ (k x x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq371917 eq42
    | exact resolve eq42 eq371917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq371940 : (k x x) = (τ (k (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq371917 eq222
    | exact resolve eq222 eq371917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq371917
  have eq372350 : (k (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq371936
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq371936
    | exact resolve eq371936 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371936
  have eq372353 : (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2181 eq372350
    | exact resolve eq372350 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372350
  have eq372717 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq372353 eq371940
    | exact resolve eq371940 eq372353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371940 eq372353
  have eq373124 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq372717
  have eq375893 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k (M.op x y) x) := by
    first
    | exact superpose eq344685 eq373124
    | exact resolve eq373124 eq344685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344685 eq373124
  have eq376301 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (k (M.op x y) x) := by grind
  clear eq375893
  have eq376636 : y = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | exact superpose eq28 eq376301
    | exact resolve eq376301 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq376301
  have eq426681 : x = y ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | exact superpose eq376636 eq343244
    | exact resolve eq343244 eq376636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343244 eq376636
  have eq426764 : x = y ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (k x x) := by grind
  clear eq426681
  have eq426812 : x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq426764
       have r₂ := eq1042
       grind)
    | exact resolve eq426764 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq426764
  have eq456823 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2119 x X0
       have i₂ := eq426812
       grind)
    | exact superpose eq426812 eq2119
    | (have j0 := eq2119 x X0
       grind)
    | (have r₁ := eq2119 x x
       have r₂ := eq426812
       grind)
    | exact resolve eq2119 eq426812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2119
  have eq456825 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq87 x x
       have i₂ := eq426812
       grind)
    | exact superpose eq426812 eq87
    | (have j0 := eq87 x x
       grind)
    | exact resolve eq87 eq426812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq426812
  have eq456840 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq456825
  have eq456842 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq456823 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456823
  have eq456868 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq456842 X0
       have j1 := eq14 X0 x
       grind)
    | (have r₁ := eq456842 X0
       have r₂ := eq14 X0 x
       grind)
    | exact resolve eq456842 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456842
  have eq457065 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43
       have i₂ := eq456868 x
       grind)
    | exact superpose eq456868 eq43
    | exact resolve eq43 eq456868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq457079 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq456868 y
       grind)
    | exact superpose eq456868 eq67
    | exact resolve eq67 eq456868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456868
  have eq457865 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq457079
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq457079
    | exact resolve eq457079 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457079
  have eq457866 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2181 eq457065
    | exact resolve eq457065 eq2181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2181 eq457065
  have eq457943 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq457865
    | exact resolve eq457865 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457865
  have eq490875 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq457866
       have i₂ := eq456840
       grind)
    | exact superpose eq456840 eq457866
    | exact resolve eq457866 eq456840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456840 eq457866
  have eq491135 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq490875
  have eq491139 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq491135
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq491135
    | exact resolve eq491135 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491135
  have eq491146 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq491139 eq14
    | (have j0 := eq14 X0 (σ x)
       grind)
    | (have r₁ := eq14 X0 (σ x)
       have r₂ := eq491139
       grind)
    | exact resolve eq14 eq491139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491139
  have eq491147 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq491146 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491146
  have eq491527 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq491147 eq457943
    | exact resolve eq457943 eq491147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457943 eq491147
  have eq491937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq491527
  have eq492214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq491937
    | exact resolve eq491937 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491937
  have eq492245 : x = (M.op x y) := by
    first
    | (have r₁ := eq492214
       have r₂ := eq27
       grind)
    | exact resolve eq492214 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492214
  have eq492256 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq492245 eq20
    | exact resolve eq20 eq492245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492259 : x ≠ x ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq492245 eq59
    | (have r₁ := eq59
       have r₂ := eq492245
       grind)
    | exact resolve eq59 eq492245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq492430 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq492245 eq19282
    | exact resolve eq19282 eq492245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19282
  have eq492439 : y = (k y x) ∨ x = (M.op x x) := by grind
  clear eq492259
  have eq492585 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq492256
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq492256
    | exact resolve eq492256 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492256
  have eq492596 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq492585 eq26
    | exact resolve eq26 eq492585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492824 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq492585 eq351377
    | (have r₁ := eq351377
       have r₂ := eq492585
       grind)
    | exact resolve eq351377 eq492585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351377
  have eq492895 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq492824
  have eq492906 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq492895
       have r₂ := eq27
       grind)
    | exact resolve eq492895 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492895
  have eq492968 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq492906 eq27
    | exact resolve eq27 eq492906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq493085 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq492906 eq492596
    | exact resolve eq492596 eq492906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492596
  have eq493186 : (σ y) ≠ (σ y) ∨ (σ y) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2575 y
       have i₂ := eq492439
       grind)
    | exact superpose eq492439 eq2575
    | (have j0 := eq2575 x
       grind)
    | exact resolve eq2575 eq492439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2575 eq492439
  have eq493221 : (σ y) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq493186
  have eq493248 : (σ y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq492585 eq493221
    | exact resolve eq493221 eq492585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493221
  have eq493284 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq493248
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq493248
    | exact resolve eq493248 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493248
  have eq493320 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq493284
       have r₂ := eq492968
       grind)
    | exact resolve eq493284 eq492968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493284
  have eq493339 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq492585 eq493320
    | exact resolve eq493320 eq492585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493320
  have eq493352 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq493339
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq493339
    | exact resolve eq493339 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq493339
  have eq493363 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq493352
    | exact resolve eq493352 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq493352
  have eq493372 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq492906 eq493363
    | exact resolve eq493363 eq492906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492906 eq493363
  have eq493378 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq492585 eq493372
    | exact resolve eq493372 eq492585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493372
  have eq493382 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq493378
       have r₂ := eq492968
       grind)
    | exact resolve eq493378 eq492968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493378
  have eq560477 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq492430
       grind)
    | exact superpose eq492430 eq16
    | exact resolve eq16 eq492430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492430
  have eq572090 : (τ (σ (M.op x y))) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq493382 eq560477
    | exact resolve eq560477 eq493382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493382 eq560477
  have eq572591 : (τ (σ (M.op x y))) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq572090
  have eq573024 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq572591
    | exact resolve eq572591 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq572591
  have eq573422 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq492245 eq573024
    | exact resolve eq573024 eq492245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492245 eq573024
  have eq573423 : x = (M.op x x) := by grind
  clear eq573422
  have eq574381 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x
       have i₂ := eq573423
       grind)
    | exact superpose eq573423 eq14
    | (have j0 := eq14 X0 x
       grind)
    | (have r₁ := eq14 X0 x
       have r₂ := eq573423
       grind)
    | exact resolve eq14 eq573423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574382 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq574381 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574381
  have eq574557 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq574382 y
       grind)
    | exact superpose eq574382 eq67
    | exact resolve eq67 eq574382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq574637 : ∀ X0 : G, (σ x) ≠ (σ (M.op x x)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq631 x X0
       have i₂ := eq574382 x
       grind)
    | exact superpose eq574382 eq631
    | (have j0 := eq631 x X0
       grind)
    | exact resolve eq631 eq574382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq574382
  have eq575267 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq574637 X0
       have i₂ := eq573423
       grind)
    | exact superpose eq573423 eq574637
    | (have j0 := eq574637 X0
       grind)
    | exact resolve eq574637 eq573423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573423 eq574637
  have eq575268 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq575267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575267
  have eq575296 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq492585 eq574557
    | exact resolve eq574557 eq492585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574557
  have eq575614 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq575268 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq575268
    | (have j0 := eq575268 X0
       grind)
    | exact resolve eq575268 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq575268
  have eq575641 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq575296
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq575296
    | exact resolve eq575296 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq575296
  have eq575846 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq492585 eq575614
    | exact resolve eq575614 eq492585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492585 eq575614
  have eq575873 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq575641
    | exact resolve eq575641 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq575641
  have eq581987 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq575846 eq575873
    | exact resolve eq575873 eq575846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575846 eq575873
  have eq582556 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq493085 eq581987
    | exact resolve eq581987 eq493085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493085 eq581987
  have eq582713 : False := by grind
  exact eq582713

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else if m(X,X) = X then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_x_y_pxx_x_pyx_pxx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = b ∨ a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq86 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq11
    | (have j0 := eq11 X1 (σ X0)
       grind)
    | exact resolve eq11 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X0) X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq87
    | (have j0 := eq87 (σ X0) X1
       grind)
    | exact resolve eq87 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq235
    | (have j0 := eq235 X0 X1
       grind)
    | exact resolve eq235 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq256 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq248 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq248
    | (have j0 := eq248 X0 X1
       grind)
    | exact resolve eq248 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq463 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq256 x y
       grind)
    | exact superpose eq256 eq16
    | (have j1 := eq256 x y
       grind)
    | exact resolve eq16 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq1572 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq463
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq463
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq463
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq463
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq463 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq1573 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq1572
  have eq38390 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1573
       grind)
    | exact superpose eq1573 eq9
    | exact resolve eq9 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq38599 : y = (M.op y y) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq38390
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq38390
    | exact resolve eq38390 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38390
  have eq38600 : (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq38599
  have eq38607 : (M.op x x) = (τ (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq38600
       grind)
    | exact superpose eq38600 eq9
    | exact resolve eq9 eq38600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38600
  have eq38816 : x = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq38607
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq38607
    | exact resolve eq38607 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38607
  have eq38817 : y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq38816
  have eq38820 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq87 y X0
       have i₂ := eq38817
       grind)
    | exact superpose eq38817 eq87
    | (have j0 := eq87 y X0
       grind)
    | (have r₁ := eq87 y x
       have r₂ := eq38817
       grind)
    | (have r₁ := eq87 x x
       have r₂ := eq38817
       grind)
    | exact resolve eq87 eq38817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq38822 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq105 y X0
       have i₂ := eq38817
       grind)
    | exact superpose eq38817 eq105
    | (have j0 := eq105 y X0
       grind)
    | exact resolve eq105 eq38817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq38817
  have eq38841 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38822 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38822
  have eq38843 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = X0 ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38820 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38820
  have eq39728 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ (τ X0) = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq19 X0 y
       have i₂ := eq38843 (τ X0)
       grind)
    | exact superpose eq38843 eq19
    | (have j1 := eq38843 (τ X0)
       grind)
    | exact resolve eq19 eq38843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq38843
  have eq48396 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y X0)) ∨ (σ X0) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38841 (σ X0)
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq38841
    | (have j0 := eq38841 (σ X0)
       grind)
    | exact resolve eq38841 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38841
  have eq119249 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 y)) ∨ y = X0 ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq39728 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39728
    | exact resolve eq39728 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39728
  have eq119573 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ y = X0 ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq119249 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq119249
    | (have j0 := eq119249 X0
       grind)
    | exact resolve eq119249 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119249
  have eq491298 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq48396 x
       grind)
    | exact superpose eq48396 eq16
    | (have j1 := eq48396 x
       grind)
    | exact resolve eq16 eq48396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48396
  have eq491325 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq491298
  have eq491545 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq491325
       have i₂ := eq119573 x
       grind)
    | exact superpose eq119573 eq491325
    | (have j1 := eq119573 x
       grind)
    | (have r₁ := eq491325
       have r₂ := eq119573 x
       grind)
    | exact resolve eq491325 eq119573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119573 eq491325
  have eq491548 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq491545
  have eq491549 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq491548
  have eq493238 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11 X0 x
       have i₂ := eq491549
       grind)
    | exact superpose eq491549 eq11
    | (have j0 := eq11 X0 x
       grind)
    | (have r₁ := eq11 X0 x
       have r₂ := eq491549
       grind)
    | exact resolve eq11 eq491549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493239 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq86 x X0
       have i₂ := eq491549
       grind)
    | exact superpose eq491549 eq86
    | (have j0 := eq86 x X0
       grind)
    | exact resolve eq86 eq491549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq491549
  have eq493264 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq493239 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493239
  have eq493265 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq493238 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493238
  have eq493446 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op x (τ X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq493265 (τ X0)
       grind)
    | exact superpose eq493265 eq18
    | exact resolve eq18 eq493265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq493265
  have eq494382 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq493264 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq493264
    | exact resolve eq493264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493264
  have eq497129 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq493446 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq493446
    | exact resolve eq493446 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493446
  have eq498077 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq497129 X0
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq497129
    | exact resolve eq497129 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497129
  have eq501708 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq494382 y
       grind)
    | exact superpose eq494382 eq16
    | exact resolve eq16 eq494382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494382
  have eq501929 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq501708
       have r₂ := eq498077 y
       grind)
    | exact resolve eq501708 eq498077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498077 eq501708
  have eq501972 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq501929
       grind)
    | exact superpose eq501929 eq9
    | exact resolve eq9 eq501929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501929
  have eq502873 : x = y ∨ x = y := by
    first
    | (have i₁ := eq501972
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq501972
    | exact resolve eq501972 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501972
  have eq502874 : x = y := by grind
  clear eq502873
  have eq502876 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq502874
       grind)
    | exact superpose eq502874 eq16
    | exact resolve eq16 eq502874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502874
  have eq502877 : False := by grind
  exact eq502877

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,Y) else if m(X,X) = X then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_x_y_pxx_x_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = b ∨ a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq86 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq11
    | (have j0 := eq11 X1 (σ X0)
       grind)
    | exact resolve eq11 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X0) X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq87
    | (have j0 := eq87 (σ X0) X1
       grind)
    | exact resolve eq87 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq235
    | (have j0 := eq235 X0 X1
       grind)
    | exact resolve eq235 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq256 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq248 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq248
    | (have j0 := eq248 X0 X1
       grind)
    | exact resolve eq248 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq463 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq256 x y
       grind)
    | exact superpose eq256 eq16
    | (have j1 := eq256 x y
       grind)
    | exact resolve eq16 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq1572 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq463
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq463
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq463
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq463
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq463 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq1573 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq1572
  have eq38390 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1573
       grind)
    | exact superpose eq1573 eq9
    | exact resolve eq9 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq38599 : y = (M.op y y) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq38390
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq38390
    | exact resolve eq38390 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38390
  have eq38600 : (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq38599
  have eq38607 : (M.op x x) = (τ (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq38600
       grind)
    | exact superpose eq38600 eq9
    | exact resolve eq9 eq38600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38600
  have eq38816 : x = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq38607
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq38607
    | exact resolve eq38607 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38607
  have eq38817 : y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq38816
  have eq38820 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq87 y X0
       have i₂ := eq38817
       grind)
    | exact superpose eq38817 eq87
    | (have j0 := eq87 y X0
       grind)
    | (have r₁ := eq87 y x
       have r₂ := eq38817
       grind)
    | (have r₁ := eq87 x x
       have r₂ := eq38817
       grind)
    | exact resolve eq87 eq38817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq38822 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq105 y X0
       have i₂ := eq38817
       grind)
    | exact superpose eq38817 eq105
    | (have j0 := eq105 y X0
       grind)
    | exact resolve eq105 eq38817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq38817
  have eq38841 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38822 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38822
  have eq38843 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = X0 ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38820 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38820
  have eq39728 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ (τ X0) = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq19 X0 y
       have i₂ := eq38843 (τ X0)
       grind)
    | exact superpose eq38843 eq19
    | (have j1 := eq38843 (τ X0)
       grind)
    | exact resolve eq19 eq38843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq38843
  have eq48396 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y X0)) ∨ (σ X0) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38841 (σ X0)
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq38841
    | (have j0 := eq38841 (σ X0)
       grind)
    | exact resolve eq38841 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38841
  have eq119249 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 y)) ∨ y = X0 ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq39728 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39728
    | exact resolve eq39728 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39728
  have eq119573 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ y = X0 ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq119249 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq119249
    | (have j0 := eq119249 X0
       grind)
    | exact resolve eq119249 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119249
  have eq491298 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq48396 x
       grind)
    | exact superpose eq48396 eq16
    | (have j1 := eq48396 x
       grind)
    | exact resolve eq16 eq48396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48396
  have eq491325 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq491298
  have eq491545 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq491325
       have i₂ := eq119573 x
       grind)
    | exact superpose eq119573 eq491325
    | (have j1 := eq119573 x
       grind)
    | (have r₁ := eq491325
       have r₂ := eq119573 x
       grind)
    | exact resolve eq491325 eq119573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119573 eq491325
  have eq491548 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq491545
  have eq491549 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq491548
  have eq493238 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11 X0 x
       have i₂ := eq491549
       grind)
    | exact superpose eq491549 eq11
    | (have j0 := eq11 X0 x
       grind)
    | (have r₁ := eq11 X0 x
       have r₂ := eq491549
       grind)
    | exact resolve eq11 eq491549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493239 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq86 x X0
       have i₂ := eq491549
       grind)
    | exact superpose eq491549 eq86
    | (have j0 := eq86 x X0
       grind)
    | exact resolve eq86 eq491549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq491549
  have eq493264 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq493239 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493239
  have eq493265 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq493238 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493238
  have eq493446 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op x (τ X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq493265 (τ X0)
       grind)
    | exact superpose eq493265 eq18
    | exact resolve eq18 eq493265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq493265
  have eq494382 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq493264 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq493264
    | exact resolve eq493264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493264
  have eq497129 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq493446 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq493446
    | exact resolve eq493446 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493446
  have eq498077 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq497129 X0
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq497129
    | exact resolve eq497129 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497129
  have eq501708 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq494382 y
       grind)
    | exact superpose eq494382 eq16
    | exact resolve eq16 eq494382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494382
  have eq501929 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq501708
       have r₂ := eq498077 y
       grind)
    | exact resolve eq501708 eq498077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498077 eq501708
  have eq501972 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq501929
       grind)
    | exact superpose eq501929 eq9
    | exact resolve eq9 eq501929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501929
  have eq502873 : x = y ∨ x = y := by
    first
    | (have i₁ := eq501972
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq501972
    | exact resolve eq501972 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501972
  have eq502874 : x = y := by grind
  clear eq502873
  have eq502876 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq502874
       grind)
    | exact superpose eq502874 eq16
    | exact resolve eq16 eq502874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502874
  have eq502877 : False := by grind
  exact eq502877

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(Y,X) else if m(X,X) = X then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_x_y_pxx_x_pyx_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = b ∨ a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq28 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 (k X0 X1) (M.op X1 X0)
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X0) (k X0 X1)
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       have j1 := eq28 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq29 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq29 X1 X0
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq29 X0 X1
       have r₂ := eq28 (k X0 X1) (M.op X1 X0)
       grind)
    | exact resolve eq29 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq32 : x = (τ (σ x)) := by
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
  have eq34 : y = (τ (σ y)) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq43 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq62 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 x)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq16
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 y)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq62 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq62
    | exact resolve eq62 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq155 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq75 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq75
    | exact resolve eq75 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq177 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq178 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq177 X0
       grind)
    | exact superpose eq177 eq14
    | (have j0 := eq14 X1 X0
       grind)
    | exact resolve eq14 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq177 X0
       grind)
    | exact superpose eq177 eq30
    | (have j0 := eq30 X0 X1
       grind)
    | exact resolve eq30 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq531 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq178 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq178
    | (have j0 := eq178 (σ X0) X1
       grind)
    | exact resolve eq178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq530 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq530
    | (have j0 := eq530 (σ X0) X1
       grind)
    | exact resolve eq530 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq979 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq980 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq985 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq980
       have i₂ := eq177 sF2
       grind)
    | exact superpose eq177 eq980
    | exact resolve eq980 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq986 : x = (k x x) ∨ (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq979
       have i₂ := eq177 x
       grind)
    | exact superpose eq177 eq979
    | exact resolve eq979 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq989 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq985
       have i₂ := eq177 sF3
       grind)
    | exact superpose eq177 eq985
    | exact resolve eq985 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq990 : (M.op x y) = (k x y) ∨ x = (k x x) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq986
       have i₂ := eq177 y
       grind)
    | exact superpose eq177 eq986
    | exact resolve eq986 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq2946 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x x) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq43 x
       have i₂ := eq990
       grind)
    | exact superpose eq990 eq43
    | exact resolve eq43 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq990
  have eq2947 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x x) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq2946
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2946
    | exact resolve eq2946 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2946
  have eq2950 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x x) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq20 eq2947
    | exact resolve eq2947 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2947
  have eq20771 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq2950 eq989
    | exact resolve eq989 eq2950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989 eq2950
  have eq20778 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ y = (k y y) ∨ x = y := by
    first
    | (have r₁ := eq20771
       have r₂ := eq27
       grind)
    | exact resolve eq20771 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20771
  have eq20788 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq20778 eq155
    | exact resolve eq155 eq20778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq20778
  have eq20803 : y = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq34 eq20788
    | exact resolve eq20788 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20788
  have eq20804 : (σ x) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by grind
  clear eq20803
  have eq20817 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq20804 eq144
    | exact resolve eq144 eq20804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq20804
  have eq20832 : x = (k x x) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq32 eq20817
    | exact resolve eq20817 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20817
  have eq20833 : y = (k y y) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20832
  have eq20849 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq533 y X0
       have i₂ := eq20833
       grind)
    | exact superpose eq20833 eq533
    | (have j0 := eq533 y X0
       grind)
    | exact resolve eq533 eq20833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq20851 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq530 y X0
       have i₂ := eq20833
       grind)
    | exact superpose eq20833 eq530
    | (have j0 := eq530 y X0
       grind)
    | (have r₁ := eq530 y x
       have r₂ := eq20833
       grind)
    | (have r₁ := eq530 x x
       have r₂ := eq20833
       grind)
    | exact resolve eq530 eq20833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq20833
  have eq20854 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq20851 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20851
  have eq20856 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq20849 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20849
  have eq20860 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20856 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20856
    | (have j0 := eq20856 X0
       grind)
    | exact resolve eq20856 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20856
  have eq21082 : (M.op x y) = (k y x) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq20854 x
       grind)
    | exact superpose eq20854 eq18
    | (have j1 := eq20854 x
       grind)
    | exact resolve eq18 eq20854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20854
  have eq21091 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq42 y
       have i₂ := eq21082
       grind)
    | exact superpose eq21082 eq42
    | exact resolve eq42 eq21082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21082
  have eq21092 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21091
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21091
    | exact resolve eq21091 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21091
  have eq21097 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq21092
    | exact resolve eq21092 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21092
  have eq21122 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20860 eq26
    | (have j1 := eq20860 (σ x)
       grind)
    | exact resolve eq26 eq20860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20860
  have eq21123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21097 eq21122
    | exact resolve eq21122 eq21097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21097 eq21122
  have eq21127 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq21123
       have r₂ := eq27
       grind)
    | exact resolve eq21123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21123
  have eq21140 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq531 x X0
       have i₂ := eq21127
       grind)
    | exact superpose eq21127 eq531
    | (have j0 := eq531 x X0
       grind)
    | exact resolve eq531 eq21127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq21142 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq178 x X0
       have i₂ := eq21127
       grind)
    | exact superpose eq21127 eq178
    | (have j0 := eq178 x X0
       grind)
    | (have r₁ := eq178 x x
       have r₂ := eq21127
       grind)
    | exact resolve eq178 eq21127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq21127
  have eq21143 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq21142 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21142
  have eq21145 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq21140 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21140
  have eq21149 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq21145 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21145
    | (have j0 := eq21145 X0
       grind)
    | exact resolve eq21145 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21145
  have eq21184 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq21143 y
       grind)
    | exact superpose eq21143 eq18
    | (have j1 := eq21143 y
       grind)
    | exact resolve eq18 eq21143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21143
  have eq21194 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq42 y
       have i₂ := eq21184
       grind)
    | exact superpose eq21184 eq42
    | exact resolve eq42 eq21184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21184
  have eq21195 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21194
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21194
    | exact resolve eq21194 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21194
  have eq21200 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq21195
    | exact resolve eq21195 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21195
  have eq21224 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21149 eq26
    | (have j1 := eq21149 (σ y)
       grind)
    | exact resolve eq26 eq21149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21149
  have eq21231 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21200 eq21224
    | exact resolve eq21224 eq21200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21200 eq21224
  have eq21234 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq21231
       have r₂ := eq27
       grind)
    | exact resolve eq21231 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21231
  have eq21237 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq21234 eq34
    | exact resolve eq34 eq21234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq21234
  have eq21330 : x = y ∨ x = y := by
    first
    | exact superpose eq32 eq21237
    | exact resolve eq21237 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq21237
  have eq21331 : x = y := by grind
  clear eq21330
  have eq21333 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21331
       grind)
    | exact superpose eq21331 eq18
    | exact resolve eq18 eq21331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq21334 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq21331
       grind)
    | exact superpose eq21331 eq24
    | exact resolve eq24 eq21331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq21331
  have eq21383 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq21334
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21334
    | exact resolve eq21334 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21334
  have eq21384 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq21333
       have i₂ := eq177 x
       grind)
    | exact superpose eq177 eq21333
    | exact resolve eq21333 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21333
  have eq21385 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21383 eq26
    | exact resolve eq26 eq21383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq21383
  have eq21479 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq21385
       have i₂ := eq177 sF2
       grind)
    | exact superpose eq177 eq21385
    | exact resolve eq21385 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq21385
  have eq21487 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq42 x
       have i₂ := eq21384
       grind)
    | exact superpose eq21384 eq42
    | exact resolve eq42 eq21384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq21384
  have eq21496 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq21487
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21487
    | exact resolve eq21487 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21487
  have eq21504 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21479 eq21496
    | exact resolve eq21496 eq21479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21479 eq21496
  have eq21512 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq21504
    | exact resolve eq21504 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq21504
  have eq21514 : False := by grind
  exact eq21514

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(Y,Y) else if m(X,X) = X then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pyy_y_x_y_pxx_x_pyx_pyy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op b b = b ∨ a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq86 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq11
    | (have j0 := eq11 X1 (σ X0)
       grind)
    | exact resolve eq11 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X0) X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq87
    | (have j0 := eq87 (σ X0) X1
       grind)
    | exact resolve eq87 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq235
    | (have j0 := eq235 X0 X1
       grind)
    | exact resolve eq235 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq256 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq248 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq248
    | (have j0 := eq248 X0 X1
       grind)
    | exact resolve eq248 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq463 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq256 x y
       grind)
    | exact superpose eq256 eq16
    | (have j1 := eq256 x y
       grind)
    | exact resolve eq16 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq1572 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq463
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq463
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq463
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq463
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq463 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq1573 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq1572
  have eq38390 : (M.op y y) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1573
       grind)
    | exact superpose eq1573 eq9
    | exact resolve eq9 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq38599 : y = (M.op y y) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq38390
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq38390
    | exact resolve eq38390 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38390
  have eq38600 : (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq38599
  have eq38607 : (M.op x x) = (τ (σ x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq38600
       grind)
    | exact superpose eq38600 eq9
    | exact resolve eq9 eq38600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38600
  have eq38816 : x = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq38607
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq38607
    | exact resolve eq38607 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38607
  have eq38817 : y = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq38816
  have eq38820 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq87 y X0
       have i₂ := eq38817
       grind)
    | exact superpose eq38817 eq87
    | (have j0 := eq87 y X0
       grind)
    | (have r₁ := eq87 y x
       have r₂ := eq38817
       grind)
    | (have r₁ := eq87 x x
       have r₂ := eq38817
       grind)
    | exact resolve eq87 eq38817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq38822 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq105 y X0
       have i₂ := eq38817
       grind)
    | exact superpose eq38817 eq105
    | (have j0 := eq105 y X0
       grind)
    | exact resolve eq105 eq38817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq38817
  have eq38841 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38822 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38822
  have eq38843 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = X0 ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38820 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38820
  have eq39728 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ (τ X0) = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq19 X0 y
       have i₂ := eq38843 (τ X0)
       grind)
    | exact superpose eq38843 eq19
    | (have j1 := eq38843 (τ X0)
       grind)
    | exact resolve eq19 eq38843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq38843
  have eq48396 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k y X0)) ∨ (σ X0) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38841 (σ X0)
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq38841
    | (have j0 := eq38841 (σ X0)
       grind)
    | exact resolve eq38841 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38841
  have eq119249 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 y)) ∨ y = X0 ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq39728 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39728
    | exact resolve eq39728 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39728
  have eq119573 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ y = X0 ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq119249 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq119249
    | (have j0 := eq119249 X0
       grind)
    | exact resolve eq119249 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119249
  have eq491298 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq48396 x
       grind)
    | exact superpose eq48396 eq16
    | (have j1 := eq48396 x
       grind)
    | exact resolve eq16 eq48396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48396
  have eq491325 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq491298
  have eq491545 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq491325
       have i₂ := eq119573 x
       grind)
    | exact superpose eq119573 eq491325
    | (have j1 := eq119573 x
       grind)
    | (have r₁ := eq491325
       have r₂ := eq119573 x
       grind)
    | exact resolve eq491325 eq119573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119573 eq491325
  have eq491548 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq491545
  have eq491549 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq491548
  have eq493238 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11 X0 x
       have i₂ := eq491549
       grind)
    | exact superpose eq491549 eq11
    | (have j0 := eq11 X0 x
       grind)
    | (have r₁ := eq11 X0 x
       have r₂ := eq491549
       grind)
    | exact resolve eq11 eq491549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493239 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq86 x X0
       have i₂ := eq491549
       grind)
    | exact superpose eq491549 eq86
    | (have j0 := eq86 x X0
       grind)
    | exact resolve eq86 eq491549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq491549
  have eq493264 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq493239 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493239
  have eq493265 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq493238 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493238
  have eq493446 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op x (τ X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18 X0 x
       have i₂ := eq493265 (τ X0)
       grind)
    | exact superpose eq493265 eq18
    | exact resolve eq18 eq493265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq493265
  have eq494382 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq493264 (σ X0)
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq493264
    | exact resolve eq493264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493264
  have eq497129 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq493446 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq493446
    | exact resolve eq493446 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493446
  have eq498077 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq497129 X0
       have i₂ := eq15 X0 x
       grind)
    | exact superpose eq15 eq497129
    | exact resolve eq497129 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497129
  have eq501708 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq494382 y
       grind)
    | exact superpose eq494382 eq16
    | exact resolve eq16 eq494382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494382
  have eq501929 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq501708
       have r₂ := eq498077 y
       grind)
    | exact resolve eq501708 eq498077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498077 eq501708
  have eq501972 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq501929
       grind)
    | exact superpose eq501929 eq9
    | exact resolve eq9 eq501929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501929
  have eq502873 : x = y ∨ x = y := by
    first
    | (have i₁ := eq501972
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq501972
    | exact resolve eq501972 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501972
  have eq502874 : x = y := by grind
  clear eq502873
  have eq502876 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq502874
       grind)
    | exact superpose eq502874 eq16
    | exact resolve eq16 eq502874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502874
  have eq502877 : False := by grind
  exact eq502877

/-- `x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_pxy_pxy_pyy_pxx_pyy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
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
