import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pxy_pyx_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq24 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (τ X0)
       have i₂ := eq21 (τ X0)
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq25 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
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
  clear eq23
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq25
    | exact resolve eq25 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25
  have eq46 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq49 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X2 X0) = (M.op X0 X2) := by
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
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq55 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq75 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq85 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq188 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq55 X1 X0
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq55 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq11 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq206 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq224 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq206 X0 X1
       have j1 := eq10 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq206 X0 X1
       have r₂ := eq10 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq206 X0 X1
       have r₂ := eq10 (σ X1) (σ X0)
       grind)
    | exact resolve eq206 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq241 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq224 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq224
    | (have j0 := eq224 X0 X1
       grind)
    | exact resolve eq224 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq254 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq241 X0 X1
       have j1 := eq204 X0 X1
       grind)
    | (have r₁ := eq241 X1 X0
       have r₂ := eq204 X0 X1
       grind)
    | (have r₁ := eq241 X1 X1
       have r₂ := eq204 X1 X1
       grind)
    | exact resolve eq241 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq241
  have eq955 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 (τ X1))) = (M.op (σ (τ X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1
       have i₂ := eq254 X0 (τ X1)
       grind)
    | (have i₁ := eq28 X0
       have i₂ := eq254 (τ X0) X1
       grind)
    | exact superpose eq254 eq28
    | (have j1 := eq254 X0 (τ X1)
       grind)
    | exact resolve eq28 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq254 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq254 X0 X1
       grind)
    | exact superpose eq254 eq8
    | (have j1 := eq254 X0 X1
       grind)
    | exact resolve eq8 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq998 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq958 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq958
    | (have j0 := eq958 X0 X1
       grind)
    | exact resolve eq958 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq999 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq955 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq955
    | (have j0 := eq955 X0 X1
       grind)
    | exact resolve eq955 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1031 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq999 X0 X1
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq999
    | (have j0 := eq999 X0 X1
       grind)
    | exact resolve eq999 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq999
  have eq2314 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq998 y x
       grind)
    | exact superpose eq998 eq14
    | (have j1 := eq998 y x
       grind)
    | exact resolve eq14 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq2446 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq2314
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq2314
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq2314 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq2448 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq2446
  have eq2457 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq11 y x
       grind)
    | (have r₁ := eq2448
       have r₂ := eq11 x y
       grind)
    | (have r₁ := eq2448
       have r₂ := eq11 y x
       grind)
    | exact resolve eq2448 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448
  have eq2458 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq10 x y
       grind)
    | (have r₁ := eq2457
       have r₂ := eq10 y x
       grind)
    | (have r₁ := eq2457
       have r₂ := eq10 x y
       grind)
    | exact resolve eq2457 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457
  have eq3678 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1
       have i₂ := eq1031 (τ X1) X0
       grind)
    | exact superpose eq1031 eq28
    | (have j1 := eq1031 (τ X1) X0
       grind)
    | exact resolve eq28 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1031
  have eq3730 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3678 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3678
    | (have j0 := eq3678 X0 X1
       grind)
    | exact resolve eq3678 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3678
  have eq4182 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq2314
       have i₂ := eq3730 x y
       grind)
    | exact superpose eq3730 eq2314
    | (have j1 := eq3730 y x
       grind)
    | exact resolve eq2314 eq3730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2314 eq3730
  have eq4279 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq4182
  have eq4280 : (M.op y y) = (M.op x x) := by grind
  clear eq4279
  have eq4607 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq85 y X0
       have i₂ := eq4280
       grind)
    | exact superpose eq4280 eq85
    | (have j0 := eq85 x X0
       grind)
    | exact resolve eq85 eq4280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq4280
  have eq18542 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4607 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq4607
    | (have j0 := eq4607 (σ X0)
       grind)
    | (have r₁ := eq4607 (σ x)
       have r₂ := eq26 x
       grind)
    | exact resolve eq4607 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4607
  have eq18564 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq18542 X0
       have i₂ := eq13 X0 y
       grind)
    | exact superpose eq13 eq18542
    | (have j0 := eq18542 X0
       grind)
    | exact resolve eq18542 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18542
  have eq52240 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have j0 := eq18564 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18564
  have eq52242 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52240
       have i₂ := eq2458
       grind)
    | exact superpose eq2458 eq52240
    | exact resolve eq52240 eq2458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2458 eq52240
  have eq52246 : False := by grind
  exact eq52246

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pxy_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq24 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (τ X0)
       have i₂ := eq21 (τ X0)
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq25 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
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
  clear eq23
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq25
    | exact resolve eq25 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq59 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq90 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq337 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq59 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq59 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq11 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq359 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq337 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq363 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq359 X0 X1
       have j1 := eq10 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq359 X0 X1
       have r₂ := eq10 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq359 X0 X1
       have r₂ := eq10 (σ X1) (σ X0)
       grind)
    | exact resolve eq359 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq375 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq363 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq363
    | (have j0 := eq363 X0 X1
       grind)
    | exact resolve eq363 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq376 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq375 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq622 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 (τ X1))) = (M.op (σ X0) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1
       have i₂ := eq376 X0 (τ X1)
       grind)
    | (have i₁ := eq28 X0
       have i₂ := eq376 (τ X0) X1
       grind)
    | exact superpose eq376 eq28
    | (have j1 := eq376 X0 (τ X1)
       grind)
    | exact resolve eq28 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq376
  have eq658 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq622 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq622
    | (have j0 := eq622 X0 X1
       grind)
    | exact resolve eq622 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq688 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq658
    | (have j0 := eq658 X0 X1
       grind)
    | exact resolve eq658 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq658
  have eq702 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq688 X0 X1
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq688 X0 X1
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq688 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq688
  have eq714 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq702 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq702
    | exact resolve eq702 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq702 X0 (σ X1)
       grind)
    | exact superpose eq702 eq13
    | exact resolve eq13 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq1331 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq725 x y
       grind)
    | exact superpose eq725 eq14
    | exact resolve eq14 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq1356 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1331
       have i₂ := eq714 x y
       grind)
    | exact superpose eq714 eq1331
    | exact resolve eq1331 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq1331
  have eq1357 : False := by grind
  exact eq1357

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pxy_pyx_pyx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq24 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (τ X0)
       have i₂ := eq21 (τ X0)
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
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
  clear eq23
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq25
    | exact resolve eq25 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25
  have eq46 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq59 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq89 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  clear eq26
  have eq335 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq59 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq59 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq11 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq361 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq335 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq365 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq361 X0 X1
       have j1 := eq10 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq361 X0 X1
       have r₂ := eq10 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq361 X0 X1
       have r₂ := eq10 (σ X1) (σ X0)
       grind)
    | exact resolve eq361 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq378 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq365 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq365
    | (have j0 := eq365 X0 X1
       grind)
    | exact resolve eq365 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq379 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq378 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq623 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (σ (k (τ X1) X0)) = (M.op (σ X0) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1
       have i₂ := eq379 X0 (τ X1)
       grind)
    | (have i₁ := eq28 X0
       have i₂ := eq379 (τ X0) X1
       grind)
    | exact superpose eq379 eq28
    | (have j1 := eq379 X0 (τ X1)
       grind)
    | exact resolve eq28 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq379
  have eq659 : ∀ X0 X1 : G, (σ (k (τ X1) X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq623 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq623
    | (have j0 := eq623 X0 X1
       grind)
    | exact resolve eq623 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq689 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq659 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq659
    | (have j0 := eq659 X0 X1
       grind)
    | exact resolve eq659 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq659
  have eq703 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq689 X0 X1
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq689 X0 X1
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq689 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq689
  have eq715 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq703 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq703
    | exact resolve eq703 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq703 X0 (σ X1)
       grind)
    | exact superpose eq703 eq13
    | exact resolve eq13 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq1499 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq729 x y
       grind)
    | exact superpose eq729 eq14
    | exact resolve eq14 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq1527 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1499
       have i₂ := eq715 x y
       grind)
    | exact superpose eq715 eq1499
    | exact resolve eq1499 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715 eq1499
  have eq1528 : False := by grind
  exact eq1528

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pxy_pyx_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq24 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (τ X0)
       have i₂ := eq21 (τ X0)
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq25 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
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
  clear eq23
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq25
    | exact resolve eq25 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq55 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq85 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq188 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq55 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq55 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq11 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq55 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq55 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq11 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq205 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq189 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq206 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq223 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq205
    | (have j0 := eq205 X0 X1
       grind)
    | exact resolve eq205 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq224 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq206 X0 X1
       have j1 := eq10 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq206 X0 X1
       have r₂ := eq10 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq206 X0 X1
       have r₂ := eq10 (σ X1) (σ X0)
       grind)
    | exact resolve eq206 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq239 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq223 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq223
    | (have j0 := eq223 X0 X1
       grind)
    | exact resolve eq223 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq240 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq239 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq241 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq224 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq224
    | (have j0 := eq224 X0 X1
       grind)
    | exact resolve eq224 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq253 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq240 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq240
    | (have j0 := eq240 X0 X1
       grind)
    | exact resolve eq240 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq254 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq253 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq959 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 (τ X1))) = (M.op (σ X0) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1
       have i₂ := eq254 X0 (τ X1)
       grind)
    | (have i₁ := eq28 X0
       have i₂ := eq254 (τ X0) X1
       grind)
    | exact superpose eq254 eq28
    | (have j1 := eq254 X0 (τ X1)
       grind)
    | exact resolve eq28 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq962 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq254 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq254 X0 X1
       grind)
    | exact superpose eq254 eq8
    | (have j1 := eq254 X0 X1
       grind)
    | exact resolve eq8 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq996 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq962 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq962
    | (have j0 := eq962 X0 X1
       grind)
    | exact resolve eq962 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq997 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq959 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq959
    | (have j0 := eq959 X0 X1
       grind)
    | exact resolve eq959 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq1028 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq997 X0 X1
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq997
    | (have j0 := eq997 X0 X1
       grind)
    | exact resolve eq997 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq997
  have eq1680 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq85
    | (have j0 := eq85 X1 (σ X0)
       grind)
    | (have r₁ := eq85 X0 (σ X0)
       have r₂ := eq26 X0
       grind)
    | exact resolve eq85 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1704 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1680 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1680
    | (have j0 := eq1680 X0 X1
       grind)
    | exact resolve eq1680 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680
  have eq2314 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq996 x y
       grind)
    | exact superpose eq996 eq14
    | (have j1 := eq996 x y
       grind)
    | exact resolve eq14 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq2642 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq241 X0 X1
       grind)
    | exact superpose eq241 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq241 X0 X1
       grind)
    | exact resolve eq11 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2644 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq241 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq2659 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2644 X0 X1
       have j1 := eq1704 X1 X0
       grind)
    | (have r₁ := eq2644 X0 X1
       have r₂ := eq1704 X0 X1
       grind)
    | (have r₁ := eq2644 X1 X0
       have r₂ := eq1704 X0 X1
       grind)
    | exact resolve eq2644 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2644
  have eq2660 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2642 X0 X1
       have j1 := eq1704 X1 X0
       grind)
    | (have r₁ := eq2642 X0 X1
       have r₂ := eq1704 X0 X1
       grind)
    | (have r₁ := eq2642 X1 X0
       have r₂ := eq1704 X0 X1
       grind)
    | exact resolve eq2642 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2642
  have eq2742 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2660 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq2660
    | (have j0 := eq2660 X0 X1
       grind)
    | exact resolve eq2660 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2660
  have eq2760 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2742 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq2742
    | (have j0 := eq2742 X0 X1
       grind)
    | exact resolve eq2742 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2742
  have eq2778 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2760 X0 X1
       have j1 := eq1704 X1 X0
       grind)
    | (have r₁ := eq2760 X0 X1
       have r₂ := eq1704 X0 X1
       grind)
    | (have r₁ := eq2760 X1 X0
       have r₂ := eq1704 X0 X1
       grind)
    | exact resolve eq2760 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704 eq2760
  have eq2793 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k X1 X0)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2778 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2778
    | (have j0 := eq2778 X0 X1
       grind)
    | exact resolve eq2778 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2778
  have eq2802 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2793 X0 X1
       have j1 := eq2659 X0 X1
       grind)
    | (have r₁ := eq2793 X0 X1
       have r₂ := eq2659 X0 X1
       grind)
    | (have r₁ := eq2793 X1 X0
       have r₂ := eq2659 X0 X1
       grind)
    | exact resolve eq2793 eq2659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2659 eq2793
  have eq3261 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1
       have i₂ := eq1028 (τ X1) X0
       grind)
    | exact superpose eq1028 eq28
    | (have j1 := eq1028 (τ X1) X0
       grind)
    | exact resolve eq28 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1028
  have eq3307 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3261 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3261
    | (have j0 := eq3261 X0 X1
       grind)
    | exact resolve eq3261 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3261
  have eq3729 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq2314
       have i₂ := eq3307 y x
       grind)
    | exact superpose eq3307 eq2314
    | (have j1 := eq3307 x y
       grind)
    | exact resolve eq2314 eq3307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2314 eq3307
  have eq3822 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq3729
  have eq3823 : (M.op x x) = (M.op y y) := by grind
  clear eq3822
  have eq4122 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq3823
       grind)
    | exact superpose eq3823 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq3823
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq3823
       grind)
    | exact resolve eq10 eq3823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4123 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq3823
       grind)
    | exact superpose eq3823 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq3823
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq3823
       grind)
    | exact resolve eq10 eq3823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4142 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq85 y X0
       have i₂ := eq3823
       grind)
    | exact superpose eq3823 eq85
    | (have j0 := eq85 x X0
       grind)
    | exact resolve eq85 eq3823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq3823
  have eq4459 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq4122 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4122
  have eq5101 : (k x y) = (M.op y x) := by
    first
    | (have j0 := eq4123 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4123
  have eq18508 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ X0)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4142 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq4142
    | (have j0 := eq4142 (σ X0)
       grind)
    | (have r₁ := eq4142 (σ x)
       have r₂ := eq26 x
       grind)
    | exact resolve eq4142 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4142
  have eq18530 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ X0)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq18508 X0
       have i₂ := eq13 X0 y
       grind)
    | exact superpose eq13 eq18508
    | (have j0 := eq18508 X0
       grind)
    | exact resolve eq18508 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18508
  have eq49638 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
    first
    | (have j0 := eq18530 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18530
  have eq49640 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq49638
       have i₂ := eq5101
       grind)
    | exact superpose eq5101 eq49638
    | exact resolve eq49638 eq5101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49638
  have eq49660 : (σ (k x y)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq2802 x y
       have i₂ := eq49640
       grind)
    | exact superpose eq49640 eq2802
    | (have j0 := eq2802 x y
       grind)
    | exact resolve eq2802 eq49640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2802 eq49640
  have eq49689 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq49660
       have i₂ := eq5101
       grind)
    | exact superpose eq5101 eq49660
    | exact resolve eq49660 eq5101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5101 eq49660
  have eq49690 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq49689
  have eq49705 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq49690
       have i₂ := eq4459
       grind)
    | exact superpose eq4459 eq49690
    | exact resolve eq49690 eq4459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4459 eq49690
  have eq49717 : False := by grind
  exact eq49717

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pxy_pyy_pxy_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
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
  have eq65 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq68 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq65 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq65 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq65 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq67 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq67 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq67 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq113 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq68 X1 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq68
    | (have j0 := eq68 X1 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq68 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq68 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq68 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq120 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq113 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq123 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq120 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq120 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq120 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq125 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq123 X0 X1
       have i₂ := eq21 X1
       grind)
    | exact superpose eq21 eq123
    | (have j0 := eq123 X0 X1
       grind)
    | exact resolve eq123 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq123
  have eq168 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq70 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq172 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       have j1 := eq125 X0 X1
       grind)
    | (have r₁ := eq168 X0 X1
       have r₂ := eq125 X0 X1
       grind)
    | (have r₁ := eq168 X1 X1
       have r₂ := eq125 X1 X1
       grind)
    | exact resolve eq168 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq168
  have eq195 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq172 (σ X0) (σ X1)
       grind)
    | exact superpose eq172 eq13
    | exact resolve eq13 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1
       have i₂ := eq172 X0 X1
       grind)
    | exact superpose eq172 eq195
    | exact resolve eq195 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq195
  have eq694 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq202 x y
       grind)
    | exact superpose eq202 eq14
    | (have r₁ := eq14
       have r₂ := eq202 x y
       grind)
    | exact resolve eq14 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq721 : False := by grind
  exact eq721

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pxy_pyy_pyx_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
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
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
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
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq99 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq198 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq195 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq195 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq195 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq195 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq195 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq380 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1
       have i₂ := eq198 (σ X1) X0
       grind)
    | (have i₁ := eq26 X0
       have i₂ := eq198 X0 (σ X0)
       grind)
    | exact superpose eq198 eq26
    | (have j1 := eq198 (σ X1) X0
       grind)
    | exact resolve eq26 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4259 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq380 X0 X1
       grind)
    | exact superpose eq380 eq8
    | (have j1 := eq380 X0 X1
       grind)
    | exact resolve eq8 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq9042 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq4259 (σ X1) X0
       grind)
    | exact superpose eq4259 eq13
    | (have j1 := eq4259 (σ X1) X0
       grind)
    | exact resolve eq13 eq4259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4259
  have eq9074 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ (M.op X1 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9042 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq9042
    | (have j0 := eq9042 X0 X1
       grind)
    | exact resolve eq9042 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9042
  have eq9119 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9074 X0 X1
       have i₂ := eq8 (M.op X1 X1)
       grind)
    | exact superpose eq8 eq9074
    | (have j0 := eq9074 X0 X1
       grind)
    | exact resolve eq9074 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9074
  have eq12873 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq9119 x y
       grind)
    | exact superpose eq9119 eq14
    | (have j1 := eq9119 y x
       grind)
    | exact resolve eq14 eq9119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9119
  have eq13114 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq12873
       have i₂ := eq198 x y
       grind)
    | exact superpose eq198 eq12873
    | (have j1 := eq198 y x
       grind)
    | exact resolve eq12873 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq12873
  have eq13116 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq13114
  have eq13117 : (M.op y y) = (M.op x x) := by grind
  clear eq13116
  have eq13234 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq13117
       grind)
    | exact superpose eq13117 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq13117
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq13117
       grind)
    | exact resolve eq10 eq13117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13267 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq99 y X0
       have i₂ := eq13117
       grind)
    | exact superpose eq13117 eq99
    | (have j0 := eq99 x X0
       grind)
    | exact resolve eq99 eq13117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq13117
  have eq13480 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq13234 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13234
  have eq28284 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13267 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq13267
    | (have j0 := eq13267 (σ X0)
       grind)
    | (have r₁ := eq13267 (σ x)
       have r₂ := eq26 x
       grind)
    | exact resolve eq13267 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13267
  have eq28308 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (σ (k y X0)) := by
    intro X0
    first
    | (have i₁ := eq28284 X0
       have i₂ := eq13 y X0
       grind)
    | exact superpose eq13 eq28284
    | (have j0 := eq28284 X0
       grind)
    | exact resolve eq28284 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28284
  have eq348522 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j0 := eq28308 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28308
  have eq348524 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq348522
       have i₂ := eq13480
       grind)
    | exact superpose eq13480 eq348522
    | exact resolve eq348522 eq13480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13480 eq348522
  have eq348527 : False := by grind
  exact eq348527

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pxy_x_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq43 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (M.op X1 X2) = X1 ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = X0 := by
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
    | (have r₁ := eq10 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X1 X2) = X1 ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X1 X1 X2
       have j1 := eq50 X1 X1 X2
       grind)
    | (have r₁ := eq43 X0 X1 X2
       have r₂ := eq50 X0 X1 X2
       grind)
    | (have r₁ := eq43 X1 X0 X2
       have r₂ := eq50 X0 X1 X2
       grind)
    | (have r₁ := eq43 X0 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq50 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq43 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq50
  have eq97 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq114 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq115 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq249 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq116 (σ X0) (σ X1)
       grind)
    | exact superpose eq116 eq13
    | (have j1 := eq116 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq116 X0 (τ X1)
       grind)
    | exact superpose eq116 eq16
    | (have j1 := eq116 X0 (τ X1)
       grind)
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq116
  have eq1625 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq254
    | exact resolve eq254 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq1697 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1625 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1625
    | (have j0 := eq1625 X0 X1
       grind)
    | exact resolve eq1625 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625
  have eq2096 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq97
    | (have j0 := eq97 X1 (σ X0)
       grind)
    | (have r₁ := eq97 X0 (σ X0)
       have r₂ := eq26 X0
       grind)
    | exact resolve eq97 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq2126 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2096 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2096
    | (have j0 := eq2096 X0 X1
       grind)
    | exact resolve eq2096 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096
  have eq2976 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq249 x y
       grind)
    | exact superpose eq249 eq14
    | (have j1 := eq249 x y
       grind)
    | exact resolve eq14 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3006 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq249 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq4471 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2976
       have i₂ := eq1697 y x
       grind)
    | exact superpose eq1697 eq2976
    | (have j1 := eq1697 (σ y) (σ x)
       grind)
    | (have r₁ := eq2976
       have r₂ := eq1697 y x
       grind)
    | exact resolve eq2976 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976
  have eq4472 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4471
  have eq4676 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4472
       grind)
    | exact superpose eq4472 eq14
    | exact resolve eq14 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4677 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq4472
       grind)
    | exact superpose eq4472 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq4472
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq4472
       grind)
    | exact resolve eq11 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4472
  have eq4678 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4677
  have eq4679 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4678
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq4678
    | exact resolve eq4678 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4678
  have eq4684 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4679
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq4679
    | exact resolve eq4679 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4679
  have eq4685 : (σ x) = (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4684
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq4684
    | exact resolve eq4684 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4684
  have eq52297 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1697 y x
       have i₂ := eq4685
       grind)
    | exact superpose eq4685 eq1697
    | (have j0 := eq1697 y x
       grind)
    | exact resolve eq1697 eq4685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4685
  have eq52344 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq52297
  have eq52368 : (σ (M.op x x)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq52344
       have r₂ := eq4676
       grind)
    | exact resolve eq52344 eq4676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4676 eq52344
  have eq53163 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2126 X0 y
       have i₂ := eq52368
       grind)
    | exact superpose eq52368 eq2126
    | (have j0 := eq2126 X0 x
       grind)
    | (have r₁ := eq2126 x y
       have r₂ := eq52368
       grind)
    | (have r₁ := eq2126 y x
       have r₂ := eq52368
       grind)
    | exact resolve eq2126 eq52368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2126 eq52368
  have eq129108 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq53163 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53163
  have eq129124 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq129108
       grind)
    | exact superpose eq129108 eq14
    | exact resolve eq14 eq129108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129108
  have eq129184 : x = (M.op x y) := by
    first
    | (have j1 := eq1697 y x
       grind)
    | (have r₁ := eq129124
       have r₂ := eq1697 y x
       grind)
    | exact resolve eq129124 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697 eq129124
  have eq129185 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq129184
       grind)
    | exact superpose eq129184 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq129184
       grind)
    | exact resolve eq11 eq129184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129186 : x = (k x y) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq129185
  have eq129372 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq3006 x y
       have i₂ := eq129186
       grind)
    | exact superpose eq129186 eq3006
    | (have j0 := eq3006 x y
       grind)
    | exact resolve eq3006 eq129186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129186
  have eq129473 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq129372
  have eq129496 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq129473
       grind)
    | exact superpose eq129473 eq14
    | exact resolve eq14 eq129473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129473
  have eq129497 : (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq129496
       have i₂ := eq129184
       grind)
    | exact superpose eq129184 eq129496
    | exact resolve eq129496 eq129184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129496
  have eq129498 : (M.op x x) = (M.op y y) := by grind
  clear eq129497
  have eq129511 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq129498
       grind)
    | exact superpose eq129498 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq129498
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq129498
       grind)
    | exact resolve eq10 eq129498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129498
  have eq129701 : (M.op x y) = (k x y) := by
    first
    | (have j0 := eq129511 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129511
  have eq129704 : x = (k x y) := by
    first
    | (have i₁ := eq129701
       have i₂ := eq129184
       grind)
    | exact superpose eq129184 eq129701
    | exact resolve eq129701 eq129184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129701
  have eq129753 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3006 x y
       have i₂ := eq129704
       grind)
    | exact superpose eq129704 eq3006
    | (have j0 := eq3006 x y
       grind)
    | exact resolve eq3006 eq129704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3006 eq129704
  have eq129854 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq129753
  have eq129884 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq129854
       grind)
    | exact superpose eq129854 eq14
    | exact resolve eq14 eq129854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129854
  have eq129888 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq129884
       have i₂ := eq129184
       grind)
    | exact superpose eq129184 eq129884
    | exact resolve eq129884 eq129184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129184 eq129884
  have eq129889 : False := by grind
  exact eq129889

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pxy_x_pyx_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
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
  have eq24 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 X0 (τ X0)
       have i₂ := eq21 (τ X0)
       grind)
    | exact superpose eq21 eq15
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq25 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
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
  clear eq23
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq25
    | exact resolve eq25 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq56 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq84 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq195 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1)
       have i₂ := eq54 X0 X1
       grind)
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq8
    | (have j1 := eq54 X0 X1
       grind)
    | exact resolve eq8 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq207 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq195
    | (have j0 := eq195 X0 X1
       grind)
    | exact resolve eq195 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq1199 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq201 (τ X0) (τ X1)
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq201
    | (have j0 := eq201 (τ X0) (τ X1)
       grind)
    | exact resolve eq201 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq201
  have eq1208 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1199 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq1199
    | (have j0 := eq1199 X0 X1
       grind)
    | exact resolve eq1199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1214 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1208 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1208
    | (have j0 := eq1208 X0 X1
       grind)
    | exact resolve eq1208 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1217 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1214 X0 X1
       have i₂ := eq28 X1
       grind)
    | exact superpose eq28 eq1214
    | (have j0 := eq1214 X0 X1
       grind)
    | exact resolve eq1214 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1218 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1217 X0 X1
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq1217
    | (have j0 := eq1217 X0 X1
       grind)
    | exact resolve eq1217 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1217
  have eq1219 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1218 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1218
    | (have j0 := eq1218 X0 X1
       grind)
    | exact resolve eq1218 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1220 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1219 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1219
    | (have j0 := eq1219 X0 X1
       grind)
    | exact resolve eq1219 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1321 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq47
    | exact resolve eq47 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1456 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1321 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1321
    | (have j0 := eq1321 X0 X1
       grind)
    | exact resolve eq1321 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1499 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq84
    | (have j0 := eq84 X1 (σ X0)
       grind)
    | (have r₁ := eq84 X0 (σ X0)
       have r₂ := eq26 X0
       grind)
    | exact resolve eq84 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1521 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1499 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1499
    | (have j0 := eq1499 X0 X1
       grind)
    | exact resolve eq1499 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1566 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq207 x y
       grind)
    | exact superpose eq207 eq14
    | (have j1 := eq207 x y
       grind)
    | exact resolve eq14 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1622 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq207 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq37712 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1566
       have i₂ := eq1456 y x
       grind)
    | exact superpose eq1456 eq1566
    | (have j1 := eq1456 x y
       grind)
    | (have r₁ := eq1566
       have r₂ := eq1456 y x
       grind)
    | exact resolve eq1566 eq1456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456 eq1566
  have eq37713 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq37712
  have eq37714 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq37713
  have eq37835 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq37714
       grind)
    | exact superpose eq37714 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq37714
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq37714
       grind)
    | exact resolve eq11 eq37714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37714
  have eq37836 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq37835
  have eq37838 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37836
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq37836
    | exact resolve eq37836 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37836
  have eq37839 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37838
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq37838
    | exact resolve eq37838 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq37838
  have eq37840 : (σ x) = (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37839
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq37839
    | exact resolve eq37839 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37839
  have eq84597 : (k x y) = (τ (σ x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq37840
       grind)
    | exact superpose eq37840 eq8
    | exact resolve eq8 eq37840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37840
  have eq84606 : (σ (M.op x x)) = (σ (M.op y y)) ∨ x = (k x y) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84597
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq84597
    | exact resolve eq84597 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84597
  have eq84607 : (M.op y y) = (τ (σ (M.op x x))) ∨ x = (k x y) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (M.op y y)
       have i₂ := eq84606
       grind)
    | exact superpose eq84606 eq8
    | exact resolve eq8 eq84606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84606
  have eq84616 : (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84607
       have i₂ := eq8 (M.op x x)
       grind)
    | exact superpose eq8 eq84607
    | exact resolve eq84607 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84607
  have eq84617 : x = (k x y) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq84616
  have eq84623 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1220 x y
       have i₂ := eq84617
       grind)
    | exact superpose eq84617 eq1220
    | (have j0 := eq1220 x y
       grind)
    | (have r₁ := eq1220 x y
       have r₂ := eq84617
       grind)
    | exact resolve eq1220 eq84617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq84617
  have eq84743 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq84623
  have eq84744 : (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq84743
  have eq84820 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq84744
       grind)
    | exact superpose eq84744 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq84744
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq84744
       grind)
    | exact resolve eq10 eq84744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84860 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1521 y X0
       have i₂ := eq84744
       grind)
    | exact superpose eq84744 eq1521
    | (have j0 := eq1521 X0 x
       grind)
    | exact resolve eq1521 eq84744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84744
  have eq85440 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq84820 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84820
  have eq86332 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq84860 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84860
  have eq86351 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq86332
       grind)
    | exact superpose eq86332 eq14
    | exact resolve eq14 eq86332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86332
  have eq86378 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86351
       have i₂ := eq85440
       grind)
    | exact superpose eq85440 eq86351
    | exact resolve eq86351 eq85440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85440 eq86351
  have eq86397 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq86378
  have eq86398 : x = (M.op x y) := by grind
  clear eq86397
  have eq86400 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq86398
       grind)
    | exact superpose eq86398 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq86398
       grind)
    | exact resolve eq11 eq86398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86407 : x = (k x y) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq86400
  have eq86563 : (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1622 x y
       have i₂ := eq86407
       grind)
    | exact superpose eq86407 eq1622
    | (have j0 := eq1622 x y
       grind)
    | exact resolve eq1622 eq86407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622 eq86407
  have eq86885 : (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq86563
  have eq86886 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq86885
  have eq86955 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq86886
       grind)
    | exact superpose eq86886 eq14
    | exact resolve eq14 eq86886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86886
  have eq86961 : (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq86955
       have i₂ := eq86398
       grind)
    | exact superpose eq86398 eq86955
    | exact resolve eq86955 eq86398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86955
  have eq86962 : (M.op x x) = (M.op y y) := by grind
  clear eq86961
  have eq87041 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq86962
       grind)
    | exact superpose eq86962 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq86962
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq86962
       grind)
    | exact resolve eq10 eq86962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87120 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1521 y X0
       have i₂ := eq86962
       grind)
    | exact superpose eq86962 eq1521
    | (have j0 := eq1521 X0 x
       grind)
    | exact resolve eq1521 eq86962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521 eq86962
  have eq87674 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq87041 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87041
  have eq87682 : x = (k y x) := by
    first
    | (have i₁ := eq87674
       have i₂ := eq86398
       grind)
    | exact superpose eq86398 eq87674
    | exact resolve eq87674 eq86398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87674
  have eq89254 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j0 := eq87120 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87120
  have eq89264 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq89254
       have i₂ := eq87682
       grind)
    | exact superpose eq87682 eq89254
    | exact resolve eq89254 eq87682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87682 eq89254
  have eq89286 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq89264
       grind)
    | exact superpose eq89264 eq14
    | exact resolve eq14 eq89264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89264
  have eq89295 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq89286
       have i₂ := eq86398
       grind)
    | exact superpose eq86398 eq89286
    | exact resolve eq89286 eq86398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86398 eq89286
  have eq89296 : False := by grind
  exact eq89296
