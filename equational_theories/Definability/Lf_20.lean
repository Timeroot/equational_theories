import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq61 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq38 x y
       grind)
    | exact superpose eq38 eq14
    | (have j1 := eq38 x y
       grind)
    | exact resolve eq14 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq294 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (τ X1) (τ X0)
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq64
    | (have j0 := eq64 (τ X1) (τ X0)
       grind)
    | exact resolve eq64 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq304 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq306 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
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
  have eq307 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X0
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
  have eq308 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq307
    | (have j0 := eq307 X0 X1
       grind)
    | exact resolve eq307 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq309 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq308
    | (have j0 := eq308 X0 X1
       grind)
    | exact resolve eq308 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq354 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (τ X1) (τ X0)
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq65
    | (have j0 := eq65 (τ X1) (τ X0)
       grind)
    | exact resolve eq65 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq361 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq364 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq366 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq364 X0 X1
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
  have eq367 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq366 X0 X0
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
  have eq368 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq367 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq367
    | (have j0 := eq367 X0 X1
       grind)
    | exact resolve eq367 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq369 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq414 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq61
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq61
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq61 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq415 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq414
  have eq2756 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq415
       grind)
    | exact superpose eq415 eq10
    | (have r₁ := eq10 (σ y) (σ x)
       have r₂ := eq415
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq415
       grind)
    | exact resolve eq10 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq2758 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2756
  have eq2759 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2758
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq2758
    | exact resolve eq2758 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2758
  have eq19245 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq2759
       grind)
    | exact superpose eq2759 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq2759
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq2759
       grind)
    | exact resolve eq11 eq2759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19246 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq2759
       grind)
    | exact superpose eq2759 eq10
    | (have r₁ := eq10 y x
       have r₂ := eq2759
       grind)
    | exact resolve eq10 eq2759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759
  have eq19247 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq19245
  have eq19249 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19246
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq19246
    | exact resolve eq19246 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19246
  have eq19250 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19247
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq19247
    | exact resolve eq19247 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19247
  have eq19252 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq19250
       have r₂ := eq19249
       grind)
    | exact resolve eq19250 eq19249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19249 eq19250
  have eq19728 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (k y x)
       have i₂ := eq19252
       grind)
    | exact superpose eq19252 eq8
    | exact resolve eq8 eq19252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19252
  have eq19875 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19728
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq19728
    | exact resolve eq19728 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19728
  have eq19878 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq369 y x
       grind)
    | (have r₁ := eq19875
       have r₂ := eq369 y x
       grind)
    | exact resolve eq19875 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq19875
  have eq20123 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (k y x)
       have i₂ := eq19878
       grind)
    | exact superpose eq19878 eq8
    | exact resolve eq8 eq19878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19878
  have eq20270 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20123
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq20123
    | exact resolve eq20123 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20123
  have eq20271 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq309 y x
       grind)
    | (have r₁ := eq20270
       have r₂ := eq309 y x
       grind)
    | exact resolve eq20270 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq20270
  have eq20500 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq20271
       grind)
    | exact superpose eq20271 eq10
    | (have r₁ := eq10 y x
       have r₂ := eq20271
       grind)
    | exact resolve eq10 eq20271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20501 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq20502 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq20500
  have eq21020 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65 x y
       have i₂ := eq20502
       grind)
    | exact superpose eq20502 eq65
    | (have j0 := eq65 x y
       grind)
    | exact resolve eq65 eq20502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq21064 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21020
  have eq26259 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21064
       grind)
    | exact superpose eq21064 eq14
    | exact resolve eq14 eq21064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21064
  have eq26935 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26259
       have i₂ := eq20271
       grind)
    | exact superpose eq20271 eq26259
    | exact resolve eq26259 eq20271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26259
  have eq26938 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq26935
  have eq26939 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26938
       have r₂ := eq20501
       grind)
    | exact resolve eq26938 eq20501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26938
  have eq27364 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq26939
       grind)
    | exact superpose eq26939 eq14
    | exact resolve eq14 eq26939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27365 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq26939
       grind)
    | exact superpose eq26939 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq26939
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq26939
       grind)
    | exact resolve eq11 eq26939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27366 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq26939
       grind)
    | exact superpose eq26939 eq10
    | exact resolve eq10 eq26939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26939
  have eq27367 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq27365
  have eq27370 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27366
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq27366
    | exact resolve eq27366 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27366
  have eq27371 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27367
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq27367
    | exact resolve eq27367 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27367
  have eq27373 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27371
       have r₂ := eq27370
       grind)
    | exact resolve eq27371 eq27370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27370 eq27371
  have eq27746 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27364
       have i₂ := eq20271
       grind)
    | exact superpose eq20271 eq27364
    | exact resolve eq27364 eq20271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20271 eq27364
  have eq27750 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27746
       have r₂ := eq20501
       grind)
    | exact resolve eq27746 eq20501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20501 eq27746
  have eq28443 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27373
       have i₂ := eq20502
       grind)
    | exact superpose eq20502 eq27373
    | exact resolve eq27373 eq20502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20502 eq27373
  have eq28595 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq28443
  have eq28653 : x = (M.op x y) := by
    first
    | (have r₁ := eq28595
       have r₂ := eq27750
       grind)
    | exact resolve eq28595 eq27750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27750 eq28595
  have eq28982 : x ≠ x ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq28653
       grind)
    | exact superpose eq28653 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq28653
       grind)
    | exact resolve eq11 eq28653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28983 : x ≠ y ∨ x = (k y x) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq28653
       grind)
    | exact superpose eq28653 eq10
    | exact resolve eq10 eq28653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28984 : x = y ∨ x = (k y x) := by grind
  clear eq28982
  have eq28985 : x = (k y x) := by
    first
    | (have r₁ := eq28984
       have r₂ := eq28983
       grind)
    | exact resolve eq28984 eq28983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28983 eq28984
  have eq29371 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq64 x y
       have i₂ := eq28985
       grind)
    | exact superpose eq28985 eq64
    | (have j0 := eq64 x y
       grind)
    | exact resolve eq64 eq28985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq29398 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29371
  have eq33972 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq29398
       grind)
    | exact superpose eq29398 eq10
    | (have r₁ := eq10 (σ y) (σ x)
       have r₂ := eq29398
       grind)
    | exact resolve eq10 eq29398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33973 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29398
  have eq33974 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33972
  have eq33975 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33974
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq33974
    | exact resolve eq33974 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33974
  have eq33978 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33975
       have i₂ := eq28985
       grind)
    | exact superpose eq28985 eq33975
    | exact resolve eq33975 eq28985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28985 eq33975
  have eq33980 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq33978
       have r₂ := eq33973
       grind)
    | exact resolve eq33978 eq33973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33973 eq33978
  have eq34411 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33980
       grind)
    | exact superpose eq33980 eq14
    | exact resolve eq14 eq33980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33980
  have eq34417 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq34411
       have i₂ := eq28653
       grind)
    | exact superpose eq28653 eq34411
    | exact resolve eq34411 eq28653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28653 eq34411
  have eq34418 : False := by grind
  exact eq34418

/-- `x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq39 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq42 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq22 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq294 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (τ X1) (τ X0)
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq42
    | (have j0 := eq42 (τ X1) (τ X0)
       grind)
    | exact resolve eq42 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq304 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq306 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
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
  have eq307 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X0
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
  have eq308 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq307
    | (have j0 := eq307 X0 X1
       grind)
    | exact resolve eq307 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq309 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq308
    | (have j0 := eq308 X0 X1
       grind)
    | exact resolve eq308 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq354 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (τ X1) (τ X0)
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq43
    | (have j0 := eq43 (τ X1) (τ X0)
       grind)
    | exact resolve eq43 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq361 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq364 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
  have eq366 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq364 X0 X1
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
  have eq367 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq366 X0 X0
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
  have eq368 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq367 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq367
    | (have j0 := eq367 X0 X1
       grind)
    | exact resolve eq367 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq369 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq414 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq39
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq414
  have eq2220 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq415
       grind)
    | exact superpose eq415 eq10
    | (have j0 := eq10 (σ y) (σ x)
       grind)
    | (have r₁ := eq10 (σ y) (σ x)
       have r₂ := eq415
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq415
       grind)
    | exact resolve eq10 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq2222 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2220
  have eq2223 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2222
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq2222
    | exact resolve eq2222 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222
  have eq17913 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq2223
       grind)
    | exact superpose eq2223 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq2223
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq2223
       grind)
    | exact resolve eq11 eq2223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17914 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq2223
       grind)
    | exact superpose eq2223 eq10
    | (have j0 := eq10 (σ y) (σ x)
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq2223
       grind)
    | exact resolve eq10 eq2223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223
  have eq17915 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq17913
  have eq17918 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17914
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq17914
    | exact resolve eq17914 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17914
  have eq17919 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq17918
  have eq17920 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17915
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq17915
    | exact resolve eq17915 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17915
  have eq17922 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17920
       have r₂ := eq17919
       grind)
    | exact resolve eq17920 eq17919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17919 eq17920
  have eq18523 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (k y x)
       have i₂ := eq17922
       grind)
    | exact superpose eq17922 eq8
    | exact resolve eq8 eq17922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17922
  have eq18672 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18523
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq18523
    | exact resolve eq18523 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18523
  have eq18675 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq369 y x
       grind)
    | (have r₁ := eq18672
       have r₂ := eq369 y x
       grind)
    | exact resolve eq18672 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq18672
  have eq18869 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8 (k y x)
       have i₂ := eq18675
       grind)
    | exact superpose eq18675 eq8
    | exact resolve eq8 eq18675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18675
  have eq19020 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18869
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq18869
    | exact resolve eq18869 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18869
  have eq19021 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq309 y x
       grind)
    | (have r₁ := eq19020
       have r₂ := eq309 y x
       grind)
    | exact resolve eq19020 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq19020
  have eq19212 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq19021
       grind)
    | exact superpose eq19021 eq10
    | (have j0 := eq10 y x
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq19021
       grind)
    | exact resolve eq10 eq19021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19213 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq19214 : x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq19212
  have eq19568 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42 x y
       have i₂ := eq19214
       grind)
    | exact superpose eq19214 eq42
    | (have j0 := eq42 x y
       grind)
    | exact resolve eq42 eq19214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq19613 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19568
  have eq25440 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq19613
       grind)
    | exact superpose eq19613 eq14
    | exact resolve eq14 eq19613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19613
  have eq26243 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25440
       have i₂ := eq19021
       grind)
    | exact superpose eq19021 eq25440
    | exact resolve eq25440 eq19021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25440
  have eq26246 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq26243
  have eq26247 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26246
       have r₂ := eq19213
       grind)
    | exact resolve eq26246 eq19213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26246
  have eq26511 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq26247
       grind)
    | exact superpose eq26247 eq14
    | exact resolve eq14 eq26247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26512 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq26247
       grind)
    | exact superpose eq26247 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq26247
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq26247
       grind)
    | exact resolve eq11 eq26247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26247
  have eq26514 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq26512
  have eq26518 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26514
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq26514
    | exact resolve eq26514 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26514
  have eq26687 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26511
       have i₂ := eq19021
       grind)
    | exact superpose eq19021 eq26511
    | exact resolve eq26511 eq19021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19021 eq26511
  have eq26691 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26687
       have r₂ := eq19213
       grind)
    | exact resolve eq26687 eq19213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19213 eq26687
  have eq26936 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26518
       have i₂ := eq19214
       grind)
    | exact superpose eq19214 eq26518
    | exact resolve eq26518 eq19214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19214 eq26518
  have eq27033 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq26936
  have eq27109 : x = (M.op x y) := by
    first
    | (have r₁ := eq27033
       have r₂ := eq26691
       grind)
    | exact resolve eq27033 eq26691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26691 eq27033
  have eq27268 : x ≠ x ∨ x = y ∨ y = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq27109
       grind)
    | exact superpose eq27109 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq27109
       grind)
    | exact resolve eq11 eq27109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27269 : x ≠ y ∨ x = (k y x) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq27109
       grind)
    | exact superpose eq27109 eq10
    | (have j0 := eq10 y x
       grind)
    | exact resolve eq10 eq27109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27270 : y = (k y x) ∨ x = y := by grind
  clear eq27268
  have eq27482 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq43 x y
       have i₂ := eq27270
       grind)
    | exact superpose eq27270 eq43
    | (have j0 := eq43 x y
       grind)
    | exact resolve eq43 eq27270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq27508 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq27482
  have eq28394 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq27508
       grind)
    | exact superpose eq27508 eq10
    | (have j0 := eq10 (σ y) (σ x)
       grind)
    | (have r₁ := eq10 (σ y) (σ x)
       have r₂ := eq27508
       grind)
    | exact resolve eq10 eq27508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27508
  have eq28396 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq28394
  have eq28397 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq28396
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq28396
    | exact resolve eq28396 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28396
  have eq28674 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq28397
       grind)
    | exact superpose eq28397 eq14
    | exact resolve eq14 eq28397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28397
  have eq28683 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq28674
       have i₂ := eq27109
       grind)
    | exact superpose eq27109 eq28674
    | exact resolve eq28674 eq27109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28674
  have eq28684 : (σ x) = (σ (k y x)) ∨ x = y := by grind
  clear eq28683
  have eq28832 : (k y x) = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 (k y x)
       have i₂ := eq28684
       grind)
    | exact superpose eq28684 eq8
    | exact resolve eq8 eq28684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28684
  have eq28984 : x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq28832
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq28832
    | exact resolve eq28832 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28832
  have eq28985 : x = (k y x) := by
    first
    | (have r₁ := eq28984
       have r₂ := eq27269
       grind)
    | exact resolve eq28984 eq27269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27269 eq28984
  have eq29128 : x = y ∨ x = y := by
    first
    | (have i₁ := eq27270
       have i₂ := eq28985
       grind)
    | exact superpose eq28985 eq27270
    | exact resolve eq27270 eq28985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27270
  have eq29159 : x = y := by grind
  clear eq29128
  have eq29300 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29159
       grind)
    | exact superpose eq29159 eq14
    | exact resolve eq14 eq29159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29301 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq39
       have i₂ := eq29159
       grind)
    | exact superpose eq29159 eq39
    | exact resolve eq39 eq29159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq29333 : x = (M.op x x) := by
    first
    | (have i₁ := eq27109
       have i₂ := eq29159
       grind)
    | exact superpose eq29159 eq27109
    | exact resolve eq27109 eq29159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27109
  have eq29335 : x = (k x x) := by
    first
    | (have i₁ := eq28985
       have i₂ := eq29159
       grind)
    | exact superpose eq29159 eq28985
    | exact resolve eq28985 eq29159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28985 eq29159
  have eq29364 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq29301
  have eq29365 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq29364
       have i₂ := eq29335
       grind)
    | exact superpose eq29335 eq29364
    | exact resolve eq29364 eq29335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29335 eq29364
  have eq29366 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq29300
       have i₂ := eq29333
       grind)
    | exact superpose eq29333 eq29300
    | exact resolve eq29300 eq29333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29300
  have eq29367 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq29365
       have i₂ := eq29333
       grind)
    | exact superpose eq29333 eq29365
    | exact resolve eq29365 eq29333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29333 eq29365
  have eq29368 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq29367
  have eq29369 : False := by grind
  exact eq29369

/-- `x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq33 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
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
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq70 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq10
    | (have j0 := eq10 (σ X0) (σ X1)
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq10 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq104 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq222 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq108 x y
       grind)
    | exact superpose eq108 eq14
    | (have j1 := eq108 x y
       grind)
    | exact resolve eq14 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq232 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq222 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq222
    | (have j0 := eq222 X0 X1
       grind)
    | exact resolve eq222 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq222
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
  have eq262 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq410 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq226
       have i₂ := eq262 x y
       grind)
    | exact superpose eq262 eq226
    | (have j1 := eq262 (σ x) (σ y)
       grind)
    | (have r₁ := eq226
       have r₂ := eq262 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq226
       have r₂ := eq262 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq226 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq262
  have eq413 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq410
  have eq483 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq413
       grind)
    | exact superpose eq413 eq8
    | exact resolve eq8 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq522 : x = y ∨ x = y := by
    first
    | (have i₁ := eq483
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq483
    | exact resolve eq483 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq523 : x = y := by grind
  clear eq522
  have eq601 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq523
       grind)
    | exact superpose eq523 eq14
    | exact resolve eq14 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq658 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq601
       have i₂ := eq31 x
       grind)
    | exact superpose eq31 eq601
    | (have j1 := eq31 x
       grind)
    | exact resolve eq601 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq8456 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq658
       have i₂ := eq261 x
       grind)
    | exact superpose eq261 eq658
    | (have j1 := eq261 (σ x)
       grind)
    | (have r₁ := eq658
       have r₂ := eq261 x
       grind)
    | exact resolve eq658 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq8457 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq8456
  have eq8647 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq601
       have i₂ := eq8457
       grind)
    | exact superpose eq8457 eq601
    | exact resolve eq601 eq8457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8648 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (σ x) (σ x)
       have i₂ := eq8457
       grind)
    | exact superpose eq8457 eq10
    | (have r₁ := eq10 (σ x) (σ x)
       have r₂ := eq8457
       grind)
    | (have r₁ := eq10 x x
       have r₂ := eq8457
       grind)
    | exact resolve eq10 eq8457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8457
  have eq8649 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq8648
  have eq8650 : (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8649
       have i₂ := eq13 x x
       grind)
    | exact superpose eq13 eq8649
    | exact resolve eq8649 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8649
  have eq8939 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq261 x
       have i₂ := eq8650
       grind)
    | exact superpose eq8650 eq261
    | (have j0 := eq261 x
       grind)
    | exact resolve eq261 eq8650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq8650
  have eq9014 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq8939
  have eq9035 : x = (M.op x x) := by
    first
    | (have r₁ := eq9014
       have r₂ := eq8647
       grind)
    | exact resolve eq9014 eq8647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8647 eq9014
  have eq9136 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq10 x x
       have i₂ := eq9035
       grind)
    | exact superpose eq9035 eq10
    | (have r₁ := eq10 x x
       have r₂ := eq9035
       grind)
    | exact resolve eq10 eq9035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9137 : x = (k x x) := by grind
  clear eq9136
  have eq9342 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70 x
       have i₂ := eq9137
       grind)
    | exact superpose eq9137 eq70
    | (have j0 := eq70 x
       grind)
    | exact resolve eq70 eq9137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq9137
  have eq9352 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq9342
  have eq9761 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq601
       have i₂ := eq9352
       grind)
    | exact superpose eq9352 eq601
    | exact resolve eq601 eq9352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601 eq9352
  have eq9765 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq9761
       have i₂ := eq9035
       grind)
    | exact superpose eq9035 eq9761
    | exact resolve eq9761 eq9035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9035 eq9761
  have eq9766 : False := by grind
  exact eq9766

/-- `x □ y = if m(Y,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_x_x_y_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq50 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 (k (σ X1) X0) (σ (M.op (τ X0) X1))
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
    | (have r₁ := eq72 X0
       have r₂ := eq10 X0 X0
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
  have eq98 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq100 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq457 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq50
    | exact resolve eq50 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq487 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq683 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq98
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq98
       have r₂ := eq12 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq98
       have r₂ := eq12 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq98 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq684 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq683
  have eq3566 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq684
       grind)
    | exact superpose eq684 eq14
    | exact resolve eq14 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3567 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq684
       grind)
    | exact superpose eq684 eq10
    | (have r₁ := eq10 (σ y) (σ x)
       have r₂ := eq684
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq684
       grind)
    | exact resolve eq10 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq3568 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq3567
  have eq3570 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3568
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq3568
    | exact resolve eq3568 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3568
  have eq6066 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq487 x y
       have i₂ := eq3570
       grind)
    | exact superpose eq3570 eq487
    | (have j0 := eq487 x y
       grind)
    | exact resolve eq487 eq3570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq3570
  have eq6112 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6066
  have eq6136 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6112
       have r₂ := eq3566
       grind)
    | exact resolve eq6112 eq3566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566 eq6112
  have eq6252 : y ≠ y ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq6136
       grind)
    | exact superpose eq6136 eq10
    | (have r₁ := eq10 y x
       have r₂ := eq6136
       grind)
    | exact resolve eq10 eq6136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6253 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6252
  have eq6418 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
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
  have eq6421 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq6418
  have eq6422 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6421
  have eq6592 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
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
  have eq6817 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
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
  have eq6818 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
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

/-- `x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq29 X0
       have r₂ := eq10 X0 X0
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X1 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq49 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq51 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq51 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq96 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq100 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       have j1 := eq65 X0 X1
       grind)
    | (have r₁ := eq96 X0 X1
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq96 X1 X1
       have r₂ := eq65 X1 X1
       grind)
    | exact resolve eq96 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq96
  have eq119 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq100 (σ X0) (σ X1)
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
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq119
    | exact resolve eq119 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq119
  have eq1143 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq1165 : False := by grind
  exact eq1165

/-- `x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq29 X0
       have r₂ := eq10 X0 X0
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X1 X0
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X1 X0
       have j1 := eq12 X1 X0
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
  have eq51 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq51 (k X0 X0) X0
       have r₂ := eq10 X0 X0
       grind)
    | (have r₁ := eq51 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq51 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq49 (k X0 X0) X0
       have r₂ := eq10 X0 (k X0 X0)
       grind)
    | (have r₁ := eq49 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq52 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | (have r₁ := eq52 (k X0 X0) X0
       have r₂ := eq10 X0 (k X0 X0)
       grind)
    | (have r₁ := eq52 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq52 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq53 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | (have r₁ := eq53 X0 (M.op (M.op X0 X0) X0)
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  clear eq56
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq57
  have eq65 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       have j1 := eq54 X1 X0
       grind)
    | (have r₁ := eq59 X1 X0
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq59 X0 (M.op X1 X1)
       have r₂ := eq54 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq59 X1 X1
       have r₂ := eq54 (k X1 X1) X1
       grind)
    | exact resolve eq59 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq59
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq122 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq126 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq122 X0 X1
       have j1 := eq67 X1 X0
       grind)
    | (have r₁ := eq122 X1 X0
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq122 X0 X0
       have r₂ := eq67 X0 X0
       grind)
    | exact resolve eq122 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq122
  have eq149 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq126 (σ X1) (σ X0)
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
       have i₂ := eq126 X1 X0
       grind)
    | exact superpose eq126 eq149
    | exact resolve eq149 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq149
  have eq1045 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq1068 : False := by grind
  exact eq1068

/-- `x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq42 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq42 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq42 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq42 X0 X1
       grind)
    | exact resolve eq11 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq42 X0 X1
       grind)
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq10
    | (have j0 := eq10 (σ X0) (σ X1)
       have j1 := eq42 X0 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
       have r₂ := eq42 X0 X1
       grind)
    | exact resolve eq10 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq72 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       have j1 := eq10 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq69 X0 X1
       have r₂ := eq10 (σ X0) (σ X1)
       grind)
    | exact resolve eq69 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq78 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       have j1 := eq10 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq72 X1 X1
       have r₂ := eq10 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq72 X0 X1
       have r₂ := eq10 (σ X0) (σ X1)
       grind)
    | exact resolve eq72 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq77
    | (have j0 := eq77 X0 X1
       grind)
    | exact resolve eq77 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq78
    | (have j0 := eq78 X0 X1
       grind)
    | exact resolve eq78 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       have j1 := eq86 X0 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq86 X0 X1
       grind)
    | exact resolve eq88 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq88
  have eq131 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq91
    | exact resolve eq91 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq91 x y
       grind)
    | exact superpose eq91 eq14
    | exact resolve eq14 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq337 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X0)
       have i₂ := eq131 X0 (τ X1)
       grind)
    | exact superpose eq131 eq16
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq131
  have eq362 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq337
    | exact resolve eq337 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq374 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq362 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq362
    | exact resolve eq362 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq536 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq142
       have i₂ := eq374 x y
       grind)
    | exact superpose eq374 eq142
    | exact resolve eq142 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq374
  have eq537 : False := by grind
  exact eq537

/-- `x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq42 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq42 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq42 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq42 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq42 X0 X1
       grind)
    | exact resolve eq11 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq75 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq76 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq81 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       have j1 := eq10 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq76 X0 X1
       have r₂ := eq10 (σ X1) (σ X0)
       grind)
    | exact resolve eq76 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq129 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq88 x y
       grind)
    | exact superpose eq88 eq14
    | exact resolve eq14 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq333 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq129 X0 (τ X1)
       grind)
    | exact superpose eq129 eq15
    | exact resolve eq15 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq129
  have eq359 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq333 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq333
    | exact resolve eq333 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq371 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq359 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq359
    | exact resolve eq359 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq529 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq140
       have i₂ := eq371 x y
       grind)
    | exact superpose eq371 eq140
    | exact resolve eq140 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq371
  have eq530 : False := by grind
  exact eq530
