import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
  clear eq15
  have eq22 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq39 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq22 x y
       grind)
    | exact superpose eq22 eq14
    | (have j1 := eq22 x y
       grind)
    | exact resolve eq14 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq22 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq22 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq294 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (τ X0) (τ X1)
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq42
    | (have j0 := eq42 (τ X0) (τ X1)
       grind)
    | exact resolve eq42 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq294
    | (have j0 := eq294 X0 X1
       grind)
    | exact resolve eq294 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq304 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq301 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq301
    | (have j0 := eq301 X0 X1
       grind)
    | exact resolve eq301 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq306 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq304
    | (have j0 := eq304 X0 X1
       grind)
    | exact resolve eq304 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq307 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq306
    | (have j0 := eq306 X0 X1
       grind)
    | exact resolve eq306 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq308 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq307
    | (have j0 := eq307 X0 X1
       grind)
    | exact resolve eq307 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq309 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq308
    | (have j0 := eq308 X0 X1
       grind)
    | exact resolve eq308 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq354 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (τ X0) (τ X1)
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq43
    | (have j0 := eq43 (τ X0) (τ X1)
       grind)
    | exact resolve eq43 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq361 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq354 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq354
    | (have j0 := eq354 X0 X1
       grind)
    | exact resolve eq354 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq364 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq361
    | (have j0 := eq361 X0 X1
       grind)
    | exact resolve eq361 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq366 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq364 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq364
    | (have j0 := eq364 X0 X1
       grind)
    | exact resolve eq364 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq367 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq366 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq366
    | (have j0 := eq366 X0 X1
       grind)
    | exact resolve eq366 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq368 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq367 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq367
    | (have j0 := eq367 X0 X1
       grind)
    | exact resolve eq367 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq369 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq414 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq39
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq415 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq414
  have eq2222 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq415
       grind)
    | exact superpose eq415 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq415
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq415
       grind)
    | exact resolve eq11 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2224 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq415
  have eq2225 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2222
  have eq2226 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2225
       have r₂ := eq2224
       grind)
    | exact resolve eq2225 eq2224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224 eq2225
  have eq2228 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2226
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq2226
    | exact resolve eq2226 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2226
  have eq17907 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ x) (σ y)
       have i₂ := eq2228
       grind)
    | exact superpose eq2228 eq10
    | (have j0 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq10 (σ x) (σ y)
       have r₂ := eq2228
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq2228
       grind)
    | exact resolve eq10 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228
  have eq17908 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17907
  have eq17911 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17908
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq17908
    | exact resolve eq17908 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17908
  have eq18331 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq17911
       grind)
    | exact superpose eq17911 eq8
    | exact resolve eq8 eq17911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17911
  have eq18478 : y = (k x y) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18331
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq18331
    | exact resolve eq18331 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18331
  have eq18481 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq309 x y
       grind)
    | (have r₁ := eq18478
       have r₂ := eq309 x y
       grind)
    | exact resolve eq18478 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq18478
  have eq18675 : (k x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq18481
       grind)
    | exact superpose eq18481 eq8
    | exact resolve eq8 eq18481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18481
  have eq18824 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18675
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq18675
    | exact resolve eq18675 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18675
  have eq18825 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq369 x y
       grind)
    | (have r₁ := eq18824
       have r₂ := eq369 x y
       grind)
    | exact resolve eq18824 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq18824
  have eq19008 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18825
       grind)
    | exact superpose eq18825 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq18825
       grind)
    | exact resolve eq11 eq18825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19010 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq19011 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq19008
  have eq19012 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19011
       have r₂ := eq19010
       grind)
    | exact resolve eq19011 eq19010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19011
  have eq19403 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43 x y
       have i₂ := eq19012
       grind)
    | exact superpose eq19012 eq43
    | (have j0 := eq43 x y
       grind)
    | exact resolve eq43 eq19012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq19447 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19403
  have eq60541 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq19447
       grind)
    | exact superpose eq19447 eq14
    | exact resolve eq14 eq19447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19447
  have eq60626 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60541
       have i₂ := eq18825
       grind)
    | exact superpose eq18825 eq60541
    | exact resolve eq60541 eq18825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60541
  have eq60629 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq60626
  have eq60630 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq60629
       have r₂ := eq19010
       grind)
    | exact resolve eq60629 eq19010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60629
  have eq60667 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq60630
       grind)
    | exact superpose eq60630 eq14
    | exact resolve eq14 eq60630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60668 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ x) (σ y)
       have i₂ := eq60630
       grind)
    | exact superpose eq60630 eq10
    | (have j0 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq10 (σ x) (σ y)
       have r₂ := eq60630
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq60630
       grind)
    | exact resolve eq10 eq60630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60630
  have eq60669 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq60668
  have eq60672 : (σ y) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60669
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq60669
    | exact resolve eq60669 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60669
  have eq60711 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60667
       have i₂ := eq18825
       grind)
    | exact superpose eq18825 eq60667
    | exact resolve eq60667 eq18825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18825 eq60667
  have eq60715 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq60711
       have r₂ := eq19010
       grind)
    | exact resolve eq60711 eq19010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19010 eq60711
  have eq60767 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60672
       have i₂ := eq19012
       grind)
    | exact superpose eq19012 eq60672
    | exact resolve eq60672 eq19012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19012
  have eq60803 : (k x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq60672
       grind)
    | exact superpose eq60672 eq8
    | exact resolve eq8 eq60672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60672
  have eq60890 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq60767
  have eq60947 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60803
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq60803
    | exact resolve eq60803 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60803
  have eq60974 : x = (M.op x y) := by
    first
    | (have r₁ := eq60890
       have r₂ := eq60715
       grind)
    | exact resolve eq60890 eq60715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60715 eq60890
  have eq60975 : y = (k x y) := by
    first
    | (have j1 := eq10 x y
       grind)
    | (have r₁ := eq60947
       have r₂ := eq10 x y
       grind)
    | exact resolve eq60947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60947
  have eq61056 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq42 x y
       have i₂ := eq60975
       grind)
    | exact superpose eq60975 eq42
    | (have j0 := eq42 x y
       grind)
    | exact resolve eq42 eq60975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq61095 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq61056
  have eq62583 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq61095
       grind)
    | exact superpose eq61095 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq61095
       grind)
    | exact resolve eq11 eq61095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62585 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq61095
  have eq62586 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq62583
  have eq62587 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq62586
       have r₂ := eq62585
       grind)
    | exact resolve eq62586 eq62585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62586
  have eq62590 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62587
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq62587
    | exact resolve eq62587 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62587
  have eq62592 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62590
       have i₂ := eq60975
       grind)
    | exact superpose eq60975 eq62590
    | exact resolve eq62590 eq60975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60975 eq62590
  have eq62593 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq62592
       have r₂ := eq62585
       grind)
    | exact resolve eq62592 eq62585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62585 eq62592
  have eq62635 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq62593
       grind)
    | exact superpose eq62593 eq14
    | exact resolve eq14 eq62593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62593
  have eq62639 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq62635
       have i₂ := eq60974
       grind)
    | exact superpose eq60974 eq62635
    | exact resolve eq62635 eq60974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60974 eq62635
  have eq62640 : False := by grind
  exact eq62640

/-- `x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_x_pyx_pyy_pyx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq29 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq29 x
       have r₂ := eq10 x x
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq49 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq51 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq51 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq58 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq53 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq55
    | (have j0 := eq55 X0 X1
       grind)
    | exact resolve eq55 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq56
    | (have j0 := eq56 X0 X1
       grind)
    | exact resolve eq56 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq56
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       have j1 := eq62 X0 X1
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq62 X0 X1
       grind)
    | exact resolve eq63 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq63
  have eq97 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq101 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       have j1 := eq65 X1 X0
       grind)
    | (have r₁ := eq97 X1 X0
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq97 X1 X1
       have r₂ := eq65 X1 X1
       grind)
    | exact resolve eq97 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq97
  have eq124 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq101 (σ X1) (σ X0)
       grind)
    | exact superpose eq101 eq13
    | exact resolve eq13 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124 X0 X1
       have i₂ := eq101 X1 X0
       grind)
    | exact superpose eq101 eq124
    | exact resolve eq124 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq124
  have eq1149 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq131 x y
       grind)
    | exact superpose eq131 eq14
    | (have r₁ := eq14
       have r₂ := eq131 x y
       grind)
    | exact resolve eq14 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq1171 : False := by grind
  exact eq1171

/-- `x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_x_pyx_x_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq10
    | (have j0 := eq10 (σ X0) (σ X1)
       have j1 := eq38 X1 X0
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
       have r₂ := eq38 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X1)
       have r₂ := eq38 X1 X1
       grind)
    | exact resolve eq10 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq76 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq204 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq79 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq79
    | exact resolve eq79 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq79 y x
       grind)
    | exact superpose eq79 eq14
    | (have j1 := eq79 y x
       grind)
    | exact resolve eq14 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq215 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq204
    | (have j0 := eq204 X0 X1
       grind)
    | exact resolve eq204 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq204
  have eq790 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq215 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq215
    | exact resolve eq215 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq950 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq790 (τ X0) X1
       grind)
    | exact superpose eq790 eq16
    | (have j1 := eq790 (τ X0) X1
       grind)
    | exact resolve eq16 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq1129 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq208
       have i₂ := eq790 x y
       grind)
    | exact superpose eq790 eq208
    | (have j1 := eq790 (σ x) (σ y)
       grind)
    | exact resolve eq208 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq790
  have eq1132 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1129
  have eq1135 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1132
       grind)
    | exact superpose eq1132 eq14
    | exact resolve eq14 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq1132
       grind)
    | exact superpose eq1132 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq1132
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq1132
       grind)
    | exact resolve eq11 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1138 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1136
  have eq1140 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1138
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq1138
    | exact resolve eq1138 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq1845 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq950 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq950
    | exact resolve eq950 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq1902 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1845 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1845
    | (have j0 := eq1845 X0 X1
       grind)
    | exact resolve eq1845 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845
  have eq13606 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq1140
       grind)
    | exact superpose eq1140 eq10
    | (have j0 := eq10 (σ y) (σ x)
       grind)
    | (have r₁ := eq10 (σ y) (σ x)
       have r₂ := eq1140
       grind)
    | exact resolve eq10 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq13607 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq13606
  have eq13608 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13607
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq13607
    | exact resolve eq13607 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13607
  have eq39461 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1132
       have i₂ := eq13608
       grind)
    | exact superpose eq13608 eq1132
    | exact resolve eq1132 eq13608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq13608
  have eq39480 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq39461
  have eq39797 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1902 x y
       have i₂ := eq39480
       grind)
    | exact superpose eq39480 eq1902
    | (have j0 := eq1902 x y
       grind)
    | exact resolve eq1902 eq39480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902 eq39480
  have eq39884 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq39797
  have eq39911 : y = (M.op x y) := by
    first
    | (have r₁ := eq39884
       have r₂ := eq1135
       grind)
    | exact resolve eq39884 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135 eq39884
  have eq40205 : y ≠ y ∨ y = (M.op y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq39911
       grind)
    | exact superpose eq39911 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq39911
       grind)
    | exact resolve eq11 eq39911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40206 : y = (k y x) ∨ y = (M.op y x) := by grind
  clear eq40205
  have eq40801 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq212 x y
       have i₂ := eq40206
       grind)
    | exact superpose eq40206 eq212
    | (have j0 := eq212 x y
       grind)
    | exact resolve eq212 eq40206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40206
  have eq40861 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq40801
  have eq41479 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq40861
       grind)
    | exact superpose eq40861 eq14
    | exact resolve eq14 eq40861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40861
  have eq41487 : (σ y) ≠ (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq41479
       have i₂ := eq39911
       grind)
    | exact superpose eq39911 eq41479
    | exact resolve eq41479 eq39911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41479
  have eq41488 : y = (M.op y x) := by grind
  clear eq41487
  have eq41803 : y ≠ y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq41488
       grind)
    | exact superpose eq41488 eq10
    | (have j0 := eq10 y x
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq41488
       grind)
    | exact resolve eq10 eq41488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41488
  have eq41811 : (M.op x y) = (k y x) := by grind
  clear eq41803
  have eq41813 : y = (k y x) := by
    first
    | (have i₁ := eq41811
       have i₂ := eq39911
       grind)
    | exact superpose eq39911 eq41811
    | exact resolve eq41811 eq39911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41811
  have eq42119 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq212 x y
       have i₂ := eq41813
       grind)
    | exact superpose eq41813 eq212
    | (have j0 := eq212 x y
       grind)
    | exact resolve eq212 eq41813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq41813
  have eq42179 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq42119
  have eq42459 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq42179
       grind)
    | exact superpose eq42179 eq14
    | exact resolve eq14 eq42179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42179
  have eq42467 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq42459
       have i₂ := eq39911
       grind)
    | exact superpose eq39911 eq42459
    | exact resolve eq42459 eq39911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39911 eq42459
  have eq42468 : False := by grind
  exact eq42468

/-- `x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_x_pyx_y_pyx_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq71 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq10
    | (have j0 := eq10 (σ X0) (σ X1)
       have j1 := eq38 X1 X0
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
       have r₂ := eq38 X0 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
       have r₂ := eq38 X0 X1
       grind)
    | exact resolve eq10 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq75 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq200 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq81
    | exact resolve eq81 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq81 y x
       grind)
    | exact superpose eq81 eq14
    | (have j1 := eq81 y x
       grind)
    | exact resolve eq14 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq10
    | (have j0 := eq10 (σ X1) (σ X0)
       have j1 := eq81 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq10 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq211 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq209 X0 X1
       have j1 := eq10 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq209 X0 X1
       have r₂ := eq10 (σ X1) (σ X0)
       grind)
    | exact resolve eq209 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq213 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq200
    | (have j0 := eq200 X0 X1
       grind)
    | exact resolve eq200 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq200
  have eq214 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq211 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq211
    | (have j0 := eq211 X0 X1
       grind)
    | exact resolve eq211 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq789 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq213 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq213
    | exact resolve eq213 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq874 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq789 (τ X1) X0
       grind)
    | exact superpose eq789 eq15
    | (have j1 := eq789 (τ X1) X0
       grind)
    | exact resolve eq15 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq961 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq206
       have i₂ := eq789 y x
       grind)
    | exact superpose eq789 eq206
    | (have j1 := eq789 (σ y) (σ x)
       grind)
    | exact resolve eq206 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq789
  have eq964 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq961
  have eq966 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq964
       grind)
    | exact superpose eq964 eq14
    | exact resolve eq14 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq964
       grind)
    | exact superpose eq964 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq964
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq964
       grind)
    | exact resolve eq11 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq968 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ x) (σ y)
       have i₂ := eq964
       grind)
    | exact superpose eq964 eq10
    | (have j0 := eq10 (σ x) (σ y)
       grind)
    | (have r₁ := eq10 (σ x) (σ y)
       have r₂ := eq964
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq964
       grind)
    | exact resolve eq10 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq969 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq968
  have eq970 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq967
  have eq971 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq969
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq969
    | exact resolve eq969 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq972 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq970
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq970
    | exact resolve eq970 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq2413 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq874 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq874
    | exact resolve eq874 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq2466 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2413 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2413
    | (have j0 := eq2413 X0 X1
       grind)
    | exact resolve eq2413 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413
  have eq14354 : (σ y) = (σ (k x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq971
       have i₂ := eq972
       grind)
    | exact superpose eq972 eq971
    | exact resolve eq971 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971 eq972
  have eq14359 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq14354
  have eq14651 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq2466 y x
       have i₂ := eq14359
       grind)
    | exact superpose eq14359 eq2466
    | (have j0 := eq2466 y x
       grind)
    | exact resolve eq2466 eq14359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14359
  have eq14708 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq14651
  have eq14736 : (σ y) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14708
       have r₂ := eq966
       grind)
    | exact resolve eq14708 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq14708
  have eq14971 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq214 x y
       have i₂ := eq14736
       grind)
    | exact superpose eq14736 eq214
    | (have j0 := eq214 x y
       grind)
    | (have r₁ := eq214 x y
       have r₂ := eq14736
       grind)
    | exact resolve eq214 eq14736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq14736
  have eq15033 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq14971
  have eq16410 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq15033
       grind)
    | exact superpose eq15033 eq14
    | exact resolve eq14 eq15033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15033
  have eq16432 : x = (M.op x y) := by
    first
    | (have j1 := eq2466 y x
       grind)
    | (have r₁ := eq16410
       have r₂ := eq2466 y x
       grind)
    | exact resolve eq16410 eq2466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466 eq16410
  have eq16659 : x ≠ x ∨ y = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq16432
       grind)
    | exact superpose eq16432 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq16432
       grind)
    | exact resolve eq11 eq16432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16662 : x = (k y x) ∨ y = (M.op y x) := by grind
  clear eq16659
  have eq16922 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq210 x y
       have i₂ := eq16662
       grind)
    | exact superpose eq16662 eq210
    | (have j0 := eq210 x y
       grind)
    | exact resolve eq210 eq16662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16662
  have eq16960 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq16922
  have eq17802 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq16960
       grind)
    | exact superpose eq16960 eq14
    | exact resolve eq14 eq16960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16960
  have eq17809 : (σ x) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq17802
       have i₂ := eq16432
       grind)
    | exact superpose eq16432 eq17802
    | exact resolve eq17802 eq16432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17802
  have eq17810 : y = (M.op y x) := by grind
  clear eq17809
  have eq18085 : y ≠ y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq17810
       grind)
    | exact superpose eq17810 eq10
    | (have j0 := eq10 y x
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq17810
       grind)
    | exact resolve eq10 eq17810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17810
  have eq18086 : (M.op x y) = (k y x) := by grind
  clear eq18085
  have eq18088 : x = (k y x) := by
    first
    | (have i₁ := eq18086
       have i₂ := eq16432
       grind)
    | exact superpose eq16432 eq18086
    | exact resolve eq18086 eq16432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18086
  have eq18371 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq210 x y
       have i₂ := eq18088
       grind)
    | exact superpose eq18088 eq210
    | (have j0 := eq210 x y
       grind)
    | exact resolve eq210 eq18088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq18088
  have eq18407 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18371
  have eq18958 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq18407
       grind)
    | exact superpose eq18407 eq14
    | exact resolve eq14 eq18407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18407
  have eq18964 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq18958
       have i₂ := eq16432
       grind)
    | exact superpose eq16432 eq18958
    | exact resolve eq18958 eq16432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16432 eq18958
  have eq18965 : False := by grind
  exact eq18965

/-- `x □ y = if m(X,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_x_x_y_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq50 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq66
    | (have j0 := eq66 X0
       grind)
    | exact resolve eq66 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq66
  have eq72 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq71
    | (have j0 := eq71 X0
       grind)
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq72 X0
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq72 x
       have r₂ := eq10 x x
       grind)
    | exact resolve eq72 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq73 (σ X0)
       grind)
    | exact superpose eq73 eq13
    | exact resolve eq13 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq75
    | exact resolve eq75 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq75
  have eq98 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq47 x y
       grind)
    | exact superpose eq47 eq14
    | (have j1 := eq47 x y
       grind)
    | exact resolve eq14 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq457 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq50
    | exact resolve eq50 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq487 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq457 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq457
    | (have j0 := eq457 X0 X1
       grind)
    | exact resolve eq457 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq683 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq98
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq98
       have r₂ := eq12 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq98
       have r₂ := eq12 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq98 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq684 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq683
  have eq3566 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq684
       grind)
    | exact superpose eq684 eq14
    | exact resolve eq14 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3567 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ x) (σ y)
       have i₂ := eq684
       grind)
    | exact superpose eq684 eq10
    | (have r₁ := eq10 (σ x) (σ y)
       have r₂ := eq684
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq684
       grind)
    | exact resolve eq10 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq3568 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq3567
  have eq3570 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3568
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq3568
    | exact resolve eq3568 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3568
  have eq6066 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq487 y x
       have i₂ := eq3570
       grind)
    | exact superpose eq3570 eq487
    | (have j0 := eq487 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq487 eq3570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq3570
  have eq6112 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6066
  have eq6136 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6112
       have r₂ := eq3566
       grind)
    | exact resolve eq6112 eq3566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566 eq6112
  have eq6252 : x ≠ x ∨ x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq6136
       grind)
    | exact superpose eq6136 eq10
    | (have r₁ := eq10 x y
       have r₂ := eq6136
       grind)
    | exact resolve eq10 eq6136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6253 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6252
  have eq6418 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq100 x y
       have i₂ := eq6253
       grind)
    | exact superpose eq6253 eq100
    | (have j0 := eq100 x y
       grind)
    | exact resolve eq100 eq6253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq6253
  have eq6421 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq6418
  have eq6422 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6421
  have eq6592 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq6422
       grind)
    | exact superpose eq6422 eq14
    | exact resolve eq14 eq6422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6422
  have eq6817 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6592
       have i₂ := eq6136
       grind)
    | exact superpose eq6136 eq6592
    | exact resolve eq6592 eq6136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6136 eq6592
  have eq6818 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6817
  have eq6819 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq6818
  have eq6841 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq6819
       grind)
    | exact superpose eq6819 eq8
    | exact resolve eq8 eq6819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6819
  have eq6902 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6841
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq6841
    | exact resolve eq6841 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6841
  have eq6903 : x = y := by grind
  clear eq6902
  have eq7032 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq6903
       grind)
    | exact superpose eq6903 eq14
    | exact resolve eq14 eq6903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6903
  have eq7033 : False := by grind
  exact eq7033

/-- `x □ y = if m(X,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_x_x_y_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq33 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq17
  have eq34 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | (have j0 := eq33 X0
       grind)
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq47 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq10
    | (have j0 := eq10 (σ X0) (σ X1)
       have j1 := eq47 X1 X0
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq10 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq104 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq104
    | (have j0 := eq104 X0 X1
       grind)
    | exact resolve eq104 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq222 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq108 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq108 y x
       grind)
    | exact superpose eq108 eq14
    | (have j1 := eq108 x y
       grind)
    | exact resolve eq14 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq232 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq222 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq222
    | (have j0 := eq222 X0 X1
       grind)
    | exact resolve eq222 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq222
  have eq238 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq34
    | exact resolve eq34 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq261 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq238 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq238
    | (have j0 := eq238 X0
       grind)
    | exact resolve eq238 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq262 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq232 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq232
    | exact resolve eq232 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq411 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq226
       have i₂ := eq262 x y
       grind)
    | exact superpose eq262 eq226
    | (have j1 := eq262 (σ x) (σ y)
       grind)
    | (have r₁ := eq226
       have r₂ := eq262 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq226
       have r₂ := eq262 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq226 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq262
  have eq414 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq411
  have eq484 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq414
       grind)
    | exact superpose eq414 eq8
    | exact resolve eq8 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq523 : x = y ∨ x = y := by
    first
    | (have i₁ := eq484
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq484
    | exact resolve eq484 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq524 : x = y := by grind
  clear eq523
  have eq602 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq524
       grind)
    | exact superpose eq524 eq14
    | exact resolve eq14 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq659 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq602
       have i₂ := eq31 x
       grind)
    | exact superpose eq31 eq602
    | (have j1 := eq31 x
       grind)
    | exact resolve eq602 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq8459 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq659
       have i₂ := eq261 x
       grind)
    | exact superpose eq261 eq659
    | (have j1 := eq261 (σ x)
       grind)
    | (have r₁ := eq659
       have r₂ := eq261 x
       grind)
    | exact resolve eq659 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq8460 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq8459
  have eq8650 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq602
       have i₂ := eq8460
       grind)
    | exact superpose eq8460 eq602
    | exact resolve eq602 eq8460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8651 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (σ x) (σ x)
       have i₂ := eq8460
       grind)
    | exact superpose eq8460 eq10
    | (have r₁ := eq10 (σ x) (σ x)
       have r₂ := eq8460
       grind)
    | (have r₁ := eq10 x x
       have r₂ := eq8460
       grind)
    | exact resolve eq10 eq8460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8460
  have eq8652 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq8651
  have eq8653 : (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8652
       have i₂ := eq13 x x
       grind)
    | exact superpose eq13 eq8652
    | exact resolve eq8652 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8652
  have eq8943 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq261 x
       have i₂ := eq8653
       grind)
    | exact superpose eq8653 eq261
    | (have j0 := eq261 x
       grind)
    | exact resolve eq261 eq8653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq8653
  have eq9018 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq8943
  have eq9039 : x = (M.op x x) := by
    first
    | (have r₁ := eq9018
       have r₂ := eq8650
       grind)
    | exact resolve eq9018 eq8650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8650 eq9018
  have eq9140 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq9039
       grind)
    | exact superpose eq9039 eq10
    | (have r₁ := eq10 x x
       have r₂ := eq9039
       grind)
    | exact resolve eq10 eq9039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9141 : x = (k x x) := by grind
  clear eq9140
  have eq9350 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70 x
       have i₂ := eq9141
       grind)
    | exact superpose eq9141 eq70
    | (have j0 := eq70 x
       grind)
    | exact resolve eq70 eq9141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq9141
  have eq9360 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq9350
  have eq9775 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq602
       have i₂ := eq9360
       grind)
    | exact superpose eq9360 eq602
    | exact resolve eq602 eq9360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq9360
  have eq9779 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq9775
       have i₂ := eq9039
       grind)
    | exact superpose eq9039 eq9775
    | exact resolve eq9775 eq9039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9039 eq9775
  have eq9780 : False := by grind
  exact eq9780

/-- `x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_y_pxx_pxy_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq29 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq29 x
       have r₂ := eq10 x x
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq51 X1 (k X1 X1)
       have r₂ := eq10 X1 X1
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq51 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq49 X0 (k X0 X0)
       have r₂ := eq10 X0 (k X0 X0)
       grind)
    | (have r₁ := eq49 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq52 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | (have r₁ := eq52 X0 (k X0 X0)
       have r₂ := eq10 X0 (k X0 X0)
       grind)
    | (have r₁ := eq52 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq52 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq53 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | (have r₁ := eq53 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq10 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq56
    | (have j0 := eq56 X0 X1
       grind)
    | exact resolve eq56 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq57
  have eq65 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       have j1 := eq54 X0 X1
       grind)
    | (have r₁ := eq59 X0 X1
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq59 X0 (M.op X0 X0)
       have r₂ := eq54 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq59 X0 X1
       have r₂ := eq54 X0 (k X0 X1)
       grind)
    | exact resolve eq59 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq59
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq64 X0 X1
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq64 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq64
  have eq122 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq126 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq122 X0 X1
       have j1 := eq67 X0 X1
       grind)
    | (have r₁ := eq122 X0 X1
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq122 X1 X1
       have r₂ := eq67 X1 X1
       grind)
    | exact resolve eq122 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq122
  have eq149 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq126 (σ X0) (σ X1)
       grind)
    | exact superpose eq126 eq13
    | exact resolve eq13 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X1
       have i₂ := eq126 X0 X1
       grind)
    | exact superpose eq126 eq149
    | exact resolve eq149 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq149
  have eq1050 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq158 x y
       grind)
    | exact superpose eq158 eq14
    | (have r₁ := eq14
       have r₂ := eq158 x y
       grind)
    | exact resolve eq14 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq1073 : False := by grind
  exact eq1073

/-- `x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_y_pxx_pyx_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq29 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq29 x
       have r₂ := eq10 x x
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq49 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq51 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq51 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq55
    | (have j0 := eq55 X0 X1
       grind)
    | exact resolve eq55 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq56
    | (have j0 := eq56 X0 X1
       grind)
    | exact resolve eq56 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq56
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       have j1 := eq62 X0 X1
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq62 X0 X1
       grind)
    | exact resolve eq63 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq63
  have eq96 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq100 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       have j1 := eq65 X1 X0
       grind)
    | (have r₁ := eq96 X1 X0
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq96 X0 X0
       have r₂ := eq65 X0 X0
       grind)
    | exact resolve eq96 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq96
  have eq119 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq100 (σ X1) (σ X0)
       grind)
    | exact superpose eq100 eq13
    | exact resolve eq13 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq119 X0 X1
       have i₂ := eq100 X1 X0
       grind)
    | exact superpose eq100 eq119
    | exact resolve eq119 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq119
  have eq1148 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq126 x y
       grind)
    | exact superpose eq126 eq14
    | (have r₁ := eq14
       have r₂ := eq126 x y
       grind)
    | exact resolve eq14 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq1170 : False := by grind
  exact eq1170
