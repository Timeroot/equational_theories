import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq19 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq20 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq19
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
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
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq34
    | (have j0 := eq34 X0 X1
       grind)
    | exact resolve eq34 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq37
    | (have j0 := eq37 (σ (k X0 X1)) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq37 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq90 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq90 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq90 X0 X1
       have r₂ := eq12 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq90 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq20 X1
       grind)
    | exact superpose eq20 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq153 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq160 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq153 X0 X1
       have j1 := eq98 X1 X0
       grind)
    | (have r₁ := eq153 X1 X0
       have r₂ := eq98 X0 X1
       grind)
    | (have r₁ := eq153 X0 X1
       have r₂ := eq98 (M.op X0 X0) (k X1 X0)
       grind)
    | (have r₁ := eq153 X0 X1
       have r₂ := eq98 (k X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq153 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq153
  have eq268 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq92 X1 (τ X0)
       grind)
    | exact superpose eq92 eq17
    | (have j1 := eq92 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq17 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq92
  have eq594 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq268 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq268
    | exact resolve eq268 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq631 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq594 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq594
    | (have j0 := eq594 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq594 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq648 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq160 x y
       grind)
    | exact superpose eq160 eq14
    | (have j1 := eq160 x y
       grind)
    | exact resolve eq14 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq1008 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq648
       have i₂ := eq631 x y
       grind)
    | exact superpose eq631 eq648
    | (have j1 := eq631 (σ x) (σ y)
       grind)
    | (have r₁ := eq648
       have r₂ := eq631 x y
       grind)
    | (have r₁ := eq648
       have r₂ := eq631 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq648
       have r₂ := eq631 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq648 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq648
  have eq1009 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1008
  have eq1123 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1009
       grind)
    | exact superpose eq1009 eq8
    | exact resolve eq8 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq1159 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1123
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1123
    | exact resolve eq1123 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1160 : x = y := by grind
  clear eq1159
  have eq1232 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1160
       grind)
    | exact superpose eq1160 eq14
    | exact resolve eq14 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq1233 : False := by grind
  exact eq1233

/-- `x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq19 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq20 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq19
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq34 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq66 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30 x y
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 x y
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq282 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq34
    | exact resolve eq34 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq310 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq282 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq282
    | (have j0 := eq282 X0 X1
       grind)
    | exact resolve eq282 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq657 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq66
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq66
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq66
       have r₂ := eq12 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq66
       have r₂ := eq12 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq66 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq658 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq657
  have eq3109 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq658
       grind)
    | exact superpose eq658 eq14
    | exact resolve eq14 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3110 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq658
       grind)
    | exact superpose eq658 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq658
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq658
       grind)
    | exact resolve eq11 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq3111 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3110
  have eq3112 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3111
  have eq3114 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3112
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq3112
    | exact resolve eq3112 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3112
  have eq5505 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq310 x y
       have i₂ := eq3114
       grind)
    | exact superpose eq3114 eq310
    | (have j0 := eq310 x y
       grind)
    | exact resolve eq310 eq3114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq5507 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8 (k y x)
       have i₂ := eq3114
       grind)
    | exact superpose eq3114 eq8
    | exact resolve eq8 eq3114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3114
  have eq5552 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq5505
  have eq5580 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5507
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq5507
    | exact resolve eq5507 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5507
  have eq5581 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5552
       have r₂ := eq3109
       grind)
    | exact resolve eq5552 eq3109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3109 eq5552
  have eq5584 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq11 y (k y x)
       grind)
    | (have r₁ := eq5580
       have r₂ := eq11 y x
       grind)
    | exact resolve eq5580 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5580
  have eq5917 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq68 x y
       have i₂ := eq5584
       grind)
    | exact superpose eq5584 eq68
    | (have j0 := eq68 x y
       grind)
    | exact resolve eq68 eq5584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq5584
  have eq5920 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5917
  have eq5921 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5920
  have eq6114 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq5921
       grind)
    | exact superpose eq5921 eq14
    | exact resolve eq14 eq5921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5921
  have eq6315 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6114
       have i₂ := eq5581
       grind)
    | exact superpose eq5581 eq6114
    | exact resolve eq6114 eq5581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5581 eq6114
  have eq6316 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6315
  have eq6317 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq6316
  have eq6479 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq6317
       grind)
    | exact superpose eq6317 eq8
    | exact resolve eq8 eq6317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6317
  have eq6558 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6479
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq6479
    | exact resolve eq6479 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6479
  have eq6559 : x = y := by grind
  clear eq6558
  have eq6726 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq6559
       grind)
    | exact superpose eq6559 eq14
    | exact resolve eq14 eq6559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6559
  have eq6727 : False := by grind
  exact eq6727

/-- `x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq10 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq19 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq20 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq19
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq31 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq66 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30 x y
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 x y
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq282 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq31
    | exact resolve eq31 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq310 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq282 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq282
    | (have j0 := eq282 X0 X1
       grind)
    | exact resolve eq282 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq658 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq66
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq66
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq66
       have r₂ := eq12 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq66
       have r₂ := eq12 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq66 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq659 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq658
  have eq3114 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq659
       grind)
    | exact superpose eq659 eq14
    | exact resolve eq14 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3115 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq659
       grind)
    | exact superpose eq659 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq659
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq659
       grind)
    | exact resolve eq11 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq3116 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3115
  have eq3117 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3116
  have eq3119 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3117
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq3117
    | exact resolve eq3117 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3117
  have eq5534 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq310 y x
       have i₂ := eq3119
       grind)
    | exact superpose eq3119 eq310
    | (have j0 := eq310 y x
       grind)
    | exact resolve eq310 eq3119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq5536 : (k y x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8 (k y x)
       have i₂ := eq3119
       grind)
    | exact superpose eq3119 eq8
    | exact resolve eq8 eq3119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119
  have eq5581 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq5534
  have eq5609 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5536
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq5536
    | exact resolve eq5536 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5536
  have eq5610 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5581
       have r₂ := eq3114
       grind)
    | exact resolve eq5581 eq3114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3114 eq5581
  have eq5613 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq11 x (k y x)
       grind)
    | (have r₁ := eq5609
       have r₂ := eq11 y x
       grind)
    | exact resolve eq5609 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5609
  have eq5946 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq68 x y
       have i₂ := eq5613
       grind)
    | exact superpose eq5613 eq68
    | (have j0 := eq68 x y
       grind)
    | exact resolve eq68 eq5613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq5613
  have eq5949 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5946
  have eq5950 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5949
  have eq6143 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq5950
       grind)
    | exact superpose eq5950 eq14
    | exact resolve eq14 eq5950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5950
  have eq6344 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6143
       have i₂ := eq5610
       grind)
    | exact superpose eq5610 eq6143
    | exact resolve eq6143 eq5610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5610 eq6143
  have eq6345 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6344
  have eq6346 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq6345
  have eq6506 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq6346
       grind)
    | exact superpose eq6346 eq8
    | exact resolve eq8 eq6346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6346
  have eq6585 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6506
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq6506
    | exact resolve eq6506 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6506
  have eq6586 : x = y := by grind
  clear eq6585
  have eq6751 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq6586
       grind)
    | exact superpose eq6586 eq14
    | exact resolve eq14 eq6586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6586
  have eq6752 : False := by grind
  exact eq6752
