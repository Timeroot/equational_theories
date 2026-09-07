import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
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
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq63 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq48 X1 (τ X0)
       grind)
    | exact superpose eq48 eq17
    | (have j1 := eq48 X1 (τ X0)
       grind)
    | exact resolve eq17 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq48 (σ X1) (σ X0)
       grind)
    | exact superpose eq48 eq13
    | (have j1 := eq48 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq253 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq63
    | exact resolve eq63 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq282 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq253 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq253
    | (have j0 := eq253 X0 X1
       grind)
    | exact resolve eq253 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq457 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq65 x y
       grind)
    | exact superpose eq65 eq14
    | (have j1 := eq65 x y
       grind)
    | exact resolve eq14 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1880 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq457
       have i₂ := eq282 x y
       grind)
    | exact superpose eq282 eq457
    | (have j1 := eq282 (σ x) (σ y)
       grind)
    | (have r₁ := eq457
       have r₂ := eq282 x y
       grind)
    | exact resolve eq457 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq1881 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1880
  have eq1886 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1881
       grind)
    | exact superpose eq1881 eq14
    | exact resolve eq14 eq1881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1887 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq1881
       grind)
    | exact superpose eq1881 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq1881
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq1881
       grind)
    | exact resolve eq11 eq1881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1888 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1887
  have eq1889 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1888
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq1888
    | exact resolve eq1888 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq14937 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq1889
  have eq14946 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14937
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq14937
    | exact resolve eq14937 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14937
  have eq70526 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1881
       have i₂ := eq14946
       grind)
    | exact superpose eq14946 eq1881
    | exact resolve eq1881 eq14946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1881 eq14946
  have eq70534 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq70526
  have eq71462 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq282 x y
       have i₂ := eq70534
       grind)
    | exact superpose eq70534 eq282
    | (have j0 := eq282 x y
       grind)
    | exact resolve eq282 eq70534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq70534
  have eq71541 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq71462
  have eq71568 : y = (M.op x y) := by
    first
    | (have r₁ := eq71541
       have r₂ := eq1886
       grind)
    | exact resolve eq71541 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886 eq71541
  have eq72499 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq71568
       grind)
    | exact superpose eq71568 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq71568
       grind)
    | exact resolve eq11 eq71568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72500 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq72499
  have eq73467 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq462 x y
       have i₂ := eq72500
       grind)
    | exact superpose eq72500 eq462
    | (have j0 := eq462 x y
       grind)
    | exact resolve eq462 eq72500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72500
  have eq73523 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq73467
  have eq75481 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq73523
       grind)
    | exact superpose eq73523 eq14
    | exact resolve eq14 eq73523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73523
  have eq75487 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq75481
       have i₂ := eq71568
       grind)
    | exact superpose eq71568 eq75481
    | exact resolve eq75481 eq71568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75481
  have eq75488 : y = (M.op x x) := by grind
  clear eq75487
  have eq76457 : (M.op x y) = (k y x) := by grind
  clear eq75488
  have eq76468 : y = (k y x) := by
    first
    | (have i₁ := eq76457
       have i₂ := eq71568
       grind)
    | exact superpose eq71568 eq76457
    | exact resolve eq76457 eq71568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76457
  have eq77484 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq462 x y
       have i₂ := eq76468
       grind)
    | exact superpose eq76468 eq462
    | (have j0 := eq462 x y
       grind)
    | exact resolve eq462 eq76468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq76468
  have eq77540 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq77484
  have eq79573 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq77540
       grind)
    | exact superpose eq77540 eq14
    | exact resolve eq14 eq77540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77540
  have eq79579 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq79573
       have i₂ := eq71568
       grind)
    | exact superpose eq71568 eq79573
    | exact resolve eq79573 eq71568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71568 eq79573
  have eq79580 : False := by grind
  exact eq79580

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq21 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq8
    | exact resolve eq8 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq48 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq48 (σ X1) (σ X0)
       grind)
    | exact superpose eq48 eq13
    | (have j1 := eq48 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq48 (τ X1) X0
       grind)
    | exact superpose eq48 eq16
    | (have j1 := eq48 (τ X1) X0
       grind)
    | exact resolve eq16 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq48
  have eq253 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq67
    | exact resolve eq67 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq282 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq253 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq253
    | (have j0 := eq253 X0 X1
       grind)
    | exact resolve eq253 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq457 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq65 x y
       grind)
    | exact superpose eq65 eq14
    | (have j1 := eq65 x y
       grind)
    | exact resolve eq14 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq773 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq462 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq462
    | (have j0 := eq462 (τ X1) (τ X0)
       grind)
    | exact resolve eq462 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq783 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq773 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq773
    | (have j0 := eq773 X0 X1
       grind)
    | exact resolve eq773 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq785 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq783 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq783
    | (have j0 := eq783 X0 X1
       grind)
    | exact resolve eq783 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq786 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq785 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq785
    | (have j0 := eq785 X0 X1
       grind)
    | exact resolve eq785 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq787 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq786 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq786
    | (have j0 := eq786 X0 X1
       grind)
    | exact resolve eq786 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq876 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq787 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq787
    | (have j0 := eq787 (τ X0) (τ X1)
       grind)
    | exact resolve eq787 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq787
  have eq1703 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 (M.op X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq876
  have eq1998 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq457
       have i₂ := eq282 y x
       grind)
    | exact superpose eq282 eq457
    | (have j1 := eq282 (σ y) (σ x)
       grind)
    | (have r₁ := eq457
       have r₂ := eq282 y x
       grind)
    | exact resolve eq457 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq1999 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1998
  have eq2004 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1999
       grind)
    | exact superpose eq1999 eq14
    | exact resolve eq14 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2005 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq1999
       grind)
    | exact superpose eq1999 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq1999
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq1999
       grind)
    | exact resolve eq11 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2006 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2005
  have eq2007 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2006
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq2006
    | exact resolve eq2006 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq15189 : (τ (M.op (σ x) (σ y))) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1703 (σ x)
       have i₂ := eq2007
       grind)
    | exact superpose eq2007 eq1703
    | exact resolve eq1703 eq2007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703 eq2007
  have eq15200 : x ≠ (τ (M.op (σ x) (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15189
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq15189
    | exact resolve eq15189 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15189
  have eq15216 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x ≠ (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15200
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq15200
    | exact resolve eq15200 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15200
  have eq15226 : x = (M.op x y) ∨ x ≠ (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15216
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq15216
    | exact resolve eq15216 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15216
  have eq15227 : x ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq15226
  have eq21961 : x ≠ (τ (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15227
       have i₂ := eq1999
       grind)
    | exact superpose eq1999 eq15227
    | exact resolve eq15227 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999 eq15227
  have eq21970 : x ≠ (τ (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq21961
  have eq21977 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21970
       have r₂ := eq8 x
       grind)
    | exact resolve eq21970 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21970
  have eq22333 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq282 y x
       have i₂ := eq21977
       grind)
    | exact superpose eq21977 eq282
    | (have j0 := eq282 y x
       grind)
    | exact resolve eq282 eq21977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq21977
  have eq22410 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq22333
  have eq22437 : x = (M.op x y) := by
    first
    | (have r₁ := eq22410
       have r₂ := eq2004
       grind)
    | exact resolve eq22410 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004 eq22410
  have eq22721 : x ≠ x ∨ y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq22437
       grind)
    | exact superpose eq22437 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq22437
       grind)
    | exact resolve eq11 eq22437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22722 : x = (k y x) ∨ y = (M.op x x) := by grind
  clear eq22721
  have eq23071 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq462 x y
       have i₂ := eq22722
       grind)
    | exact superpose eq22722 eq462
    | (have j0 := eq462 x y
       grind)
    | exact resolve eq462 eq22722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq22722
  have eq23098 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq23071
  have eq23570 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq23098
       grind)
    | exact superpose eq23098 eq14
    | exact resolve eq14 eq23098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23098
  have eq23574 : (σ x) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23570
       have i₂ := eq22437
       grind)
    | exact superpose eq22437 eq23570
    | exact resolve eq23570 eq22437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23570
  have eq23575 : y = (M.op x x) := by grind
  clear eq23574
  have eq24013 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq774 x
       have i₂ := eq23575
       grind)
    | exact superpose eq23575 eq774
    | exact resolve eq774 eq23575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774 eq23575
  have eq24024 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24013
       have i₂ := eq22437
       grind)
    | exact superpose eq22437 eq24013
    | exact resolve eq24013 eq22437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24013
  have eq24025 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24024
  have eq25115 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq24025
       grind)
    | exact superpose eq24025 eq14
    | exact resolve eq14 eq24025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24025
  have eq25119 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq25115
       have i₂ := eq22437
       grind)
    | exact superpose eq22437 eq25115
    | exact resolve eq25115 eq22437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22437 eq25115
  have eq25120 : False := by grind
  exact eq25120

/-- `x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq17
  have eq36 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35
    | (have j0 := eq35 X0
       grind)
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq57 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq60 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq57 X0 (τ X1)
       grind)
    | exact superpose eq57 eq18
    | (have j1 := eq57 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq57 (σ X0) (σ X1)
       grind)
    | exact superpose eq57 eq13
    | (have j1 := eq57 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq87 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq60
    | exact resolve eq60 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq168 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq147 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq147
    | (have j0 := eq147 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq147 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq455 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq61 x y
       grind)
    | exact superpose eq61 eq14
    | (have j1 := eq61 x y
       grind)
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq522 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq455
       have i₂ := eq168 y x
       grind)
    | exact superpose eq168 eq455
    | (have j1 := eq168 (σ x) (σ y)
       grind)
    | (have r₁ := eq455
       have r₂ := eq168 y x
       grind)
    | (have r₁ := eq455
       have r₂ := eq168 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq455
       have r₂ := eq168 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq455 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq455
  have eq523 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq522
  have eq526 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq36 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq36
    | exact resolve eq36 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq557 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq526 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq526
    | (have j0 := eq526 X0
       grind)
    | exact resolve eq526 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq559 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq523
       grind)
    | exact superpose eq523 eq8
    | exact resolve eq8 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq592 : x = y ∨ x = y := by
    first
    | (have i₁ := eq559
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq559
    | exact resolve eq559 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq593 : x = y := by grind
  clear eq592
  have eq677 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq593
       grind)
    | exact superpose eq593 eq14
    | exact resolve eq14 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq751 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq677
       have i₂ := eq34 x
       grind)
    | exact superpose eq34 eq677
    | (have j1 := eq34 x
       grind)
    | exact resolve eq677 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq9783 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq751
       have i₂ := eq557 x
       grind)
    | exact superpose eq557 eq751
    | (have j1 := eq557 (σ x)
       grind)
    | (have r₁ := eq751
       have r₂ := eq557 x
       grind)
    | exact resolve eq751 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq9785 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq9783
  have eq9912 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq9785
  have eq9918 : (M.op (σ x) (σ x)) = (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9912
       have i₂ := eq13 x x
       grind)
    | exact superpose eq13 eq9912
    | exact resolve eq9912 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9912
  have eq10309 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq677
       have i₂ := eq9918
       grind)
    | exact superpose eq9918 eq677
    | exact resolve eq677 eq9918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9918
  have eq10321 : x = (M.op x x) := by
    first
    | (have j1 := eq557 x
       grind)
    | (have r₁ := eq10309
       have r₂ := eq557 x
       grind)
    | exact resolve eq10309 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq10309
  have eq10489 : (M.op x x) = (k x x) := by grind
  have eq10491 : x = (k x x) := by
    first
    | (have i₁ := eq10489
       have i₂ := eq10321
       grind)
    | exact superpose eq10321 eq10489
    | exact resolve eq10489 eq10321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10489
  have eq10775 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq87 x
       have i₂ := eq10491
       grind)
    | exact superpose eq10491 eq87
    | (have j0 := eq87 x
       grind)
    | exact resolve eq87 eq10491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq10491
  have eq10786 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq10775
  have eq11390 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq677
       have i₂ := eq10786
       grind)
    | exact superpose eq10786 eq677
    | exact resolve eq677 eq10786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677 eq10786
  have eq11403 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq11390
       have i₂ := eq10321
       grind)
    | exact superpose eq10321 eq11390
    | exact resolve eq11390 eq10321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10321 eq11390
  have eq11404 : False := by grind
  exact eq11404

/-- `x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq17
  have eq36 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq35
    | (have j0 := eq35 X0
       grind)
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq57 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq60 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq57 X1 (τ X0)
       grind)
    | exact superpose eq57 eq18
    | (have j1 := eq57 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq61 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq57 (σ X1) (σ X0)
       grind)
    | exact superpose eq57 eq13
    | (have j1 := eq57 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq87 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq60
    | exact resolve eq60 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq169 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq148
    | (have j0 := eq148 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq148 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq456 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq61 x y
       grind)
    | exact superpose eq61 eq14
    | (have j1 := eq61 x y
       grind)
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq523 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq456
       have i₂ := eq169 x y
       grind)
    | exact superpose eq169 eq456
    | (have j1 := eq169 (σ x) (σ y)
       grind)
    | (have r₁ := eq456
       have r₂ := eq169 x y
       grind)
    | (have r₁ := eq456
       have r₂ := eq169 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq456
       have r₂ := eq169 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq456 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq456
  have eq524 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq523
  have eq527 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq36 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq36
    | exact resolve eq36 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq558 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq527 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq527
    | (have j0 := eq527 X0
       grind)
    | exact resolve eq527 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq560 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq524
       grind)
    | exact superpose eq524 eq8
    | exact resolve eq8 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq593 : x = y ∨ x = y := by
    first
    | (have i₁ := eq560
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq560
    | exact resolve eq560 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq594 : x = y := by grind
  clear eq593
  have eq678 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq594
       grind)
    | exact superpose eq594 eq14
    | exact resolve eq14 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq752 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq678
       have i₂ := eq34 x
       grind)
    | exact superpose eq34 eq678
    | (have j1 := eq34 x
       grind)
    | exact resolve eq678 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq10329 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq752
       have i₂ := eq558 x
       grind)
    | exact superpose eq558 eq752
    | (have j1 := eq558 (σ x)
       grind)
    | (have r₁ := eq752
       have r₂ := eq558 x
       grind)
    | exact resolve eq752 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq10331 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq10329
  have eq10511 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq10331
  have eq10517 : (M.op (σ x) (σ x)) = (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10511
       have i₂ := eq13 x x
       grind)
    | exact superpose eq13 eq10511
    | exact resolve eq10511 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10511
  have eq10978 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq678
       have i₂ := eq10517
       grind)
    | exact superpose eq10517 eq678
    | exact resolve eq678 eq10517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10517
  have eq10990 : x = (M.op x x) := by
    first
    | (have j1 := eq558 x
       grind)
    | (have r₁ := eq10978
       have r₂ := eq558 x
       grind)
    | exact resolve eq10978 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq10978
  have eq11284 : (M.op x x) = (k x x) := by grind
  have eq11286 : x = (k x x) := by
    first
    | (have i₁ := eq11284
       have i₂ := eq10990
       grind)
    | exact superpose eq10990 eq11284
    | exact resolve eq11284 eq10990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11284
  have eq11585 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq87 x
       have i₂ := eq11286
       grind)
    | exact superpose eq11286 eq87
    | (have j0 := eq87 x
       grind)
    | exact resolve eq87 eq11286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq11286
  have eq11596 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq11585
  have eq12138 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq678
       have i₂ := eq11596
       grind)
    | exact superpose eq11596 eq678
    | exact resolve eq678 eq11596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678 eq11596
  have eq12153 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq12138
       have i₂ := eq10990
       grind)
    | exact superpose eq10990 eq12138
    | exact resolve eq12138 eq10990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10990 eq12138
  have eq12154 : False := by grind
  exact eq12154

/-- `x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
       have r₂ := eq10 X0 x
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq32 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq30 (σ X0)
       grind)
    | exact superpose eq30 eq13
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq32
    | exact resolve eq32 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq56 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq106 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq157 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq165 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq157 X0 X1
       have j1 := eq159 X0 X1
       grind)
    | (have r₁ := eq157 X0 X1
       have r₂ := eq159 X0 X1
       grind)
    | exact resolve eq157 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq159
  have eq169 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq165 X0 X1
       have j1 := eq106 X1 (σ X0)
       grind)
    | (have r₁ := eq165 X0 (σ X0)
       have r₂ := eq106 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq165 X0 X0
       have r₂ := eq106 X0 (σ X0)
       grind)
    | exact resolve eq165 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq165
  have eq206 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq169 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq169
    | exact resolve eq169 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq169 X1 (σ X0)
       grind)
    | exact superpose eq169 eq13
    | exact resolve eq13 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq756 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq211 x y
       grind)
    | exact superpose eq211 eq14
    | exact resolve eq14 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq780 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq756
       have i₂ := eq206 y x
       grind)
    | exact superpose eq206 eq756
    | exact resolve eq756 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq756
  have eq781 : False := by grind
  exact eq781

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
       have r₂ := eq10 X0 x
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq32 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq30 (σ X0)
       grind)
    | exact superpose eq30 eq13
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq32
    | exact resolve eq32 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq56 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq106 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq156 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq164 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq156 X0 X1
       have j1 := eq106 X1 (σ X0)
       grind)
    | (have r₁ := eq156 X0 (σ X0)
       have r₂ := eq106 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq156 X0 X0
       have r₂ := eq106 X0 (σ X0)
       grind)
    | exact resolve eq156 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq156
  have eq168 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq164 X0 X1
       have j1 := eq158 X0 X1
       grind)
    | (have r₁ := eq164 X0 X1
       have r₂ := eq158 X0 X1
       grind)
    | exact resolve eq164 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq164
  have eq204 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq168 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq168
    | exact resolve eq168 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq168 X0 (σ X1)
       grind)
    | exact superpose eq168 eq13
    | exact resolve eq13 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq754 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq209 x y
       grind)
    | exact superpose eq209 eq14
    | exact resolve eq14 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq778 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq754
       have i₂ := eq204 x y
       grind)
    | exact superpose eq204 eq754
    | exact resolve eq754 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq754
  have eq779 : False := by grind
  exact eq779

/-- `x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
       have r₂ := eq10 X0 x
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq32 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq30 (σ X0)
       grind)
    | exact superpose eq30 eq13
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq32
    | exact resolve eq32 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq37 X1
       grind)
    | exact superpose eq37 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq106 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq47 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq11
    | (have j0 := eq11 X0 (σ X1)
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq11 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq115 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq106 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq124 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       have j1 := eq10 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq115 X0 X1
       have r₂ := eq10 X0 (σ X1)
       grind)
    | exact resolve eq115 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq124
    | (have j0 := eq124 X0 X1
       grind)
    | exact resolve eq124 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq132 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq131 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq143 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq384 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq132 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq132
    | (have j0 := eq132 X0 X1
       grind)
    | exact resolve eq132 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq459 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq384 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq384
    | (have j0 := eq384 X0 X1
       grind)
    | exact resolve eq384 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq384
  have eq469 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq459 X0 X1
       have j1 := eq143 X1 X0
       grind)
    | (have r₁ := eq459 X0 X0
       have r₂ := eq143 X0 X1
       grind)
    | exact resolve eq459 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq459
  have eq479 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq469 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq469
    | exact resolve eq469 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq469 (σ X0) X1
       grind)
    | exact superpose eq469 eq13
    | exact resolve eq13 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq1120 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq491 x y
       grind)
    | exact superpose eq491 eq14
    | exact resolve eq14 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq1136 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1120
       have i₂ := eq479 y x
       grind)
    | exact superpose eq479 eq1120
    | exact resolve eq1120 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq1120
  have eq1137 : False := by grind
  exact eq1137

/-- `x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
       have r₂ := eq10 X0 x
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq32 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq30 (σ X0)
       grind)
    | exact superpose eq30 eq13
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq32
    | exact resolve eq32 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32
  have eq42 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq104 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq47 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq11
    | (have j0 := eq11 X0 (σ X0)
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq11 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq117 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq104 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq127 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       have j1 := eq10 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq117 X0 X1
       have r₂ := eq10 X0 (σ X0)
       grind)
    | exact resolve eq117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq133 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq127
    | (have j0 := eq127 X0 X1
       grind)
    | exact resolve eq127 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq134 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq144 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq389 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq134 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq134
    | (have j0 := eq134 X1 X1
       grind)
    | exact resolve eq134 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq452 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq389 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq389
    | (have j0 := eq389 X0 X1
       grind)
    | exact resolve eq389 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq389
  have eq464 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq452 X0 X1
       have j1 := eq144 X1 X0
       grind)
    | (have r₁ := eq452 X0 X0
       have r₂ := eq144 X0 X1
       grind)
    | exact resolve eq452 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq452
  have eq476 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq464
    | exact resolve eq464 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq464 (σ X1) X0
       grind)
    | exact superpose eq464 eq13
    | exact resolve eq13 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq1107 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq488 x y
       grind)
    | exact superpose eq488 eq14
    | exact resolve eq14 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq1123 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1107
       have i₂ := eq476 x y
       grind)
    | exact superpose eq476 eq1107
    | exact resolve eq1107 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq1107
  have eq1124 : False := by grind
  exact eq1124
