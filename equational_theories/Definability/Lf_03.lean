import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | exact resolve eq32 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq37
    | (have j0 := eq37 (σ (k X0 X1)) (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq37 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq72 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq69 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq69 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq69 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq69 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq151 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq158 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq151 X1 X0
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq151 X0 X1
       have r₂ := eq77 (k X1 X0) (M.op X1 X1)
       grind)
    | (have r₁ := eq151 X0 X1
       have r₂ := eq77 (M.op X1 X1) (k X1 X0)
       grind)
    | exact resolve eq151 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq151
  have eq276 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq72 (τ X1) X0
       grind)
    | exact superpose eq72 eq16
    | (have j1 := eq72 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq72
  have eq575 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq276
    | exact resolve eq276 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq612 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq575 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq575
    | (have j0 := eq575 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq575 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq629 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq158 x y
       grind)
    | exact superpose eq158 eq14
    | (have j1 := eq158 x y
       grind)
    | exact resolve eq14 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq1063 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq629
       have i₂ := eq612 y x
       grind)
    | exact superpose eq612 eq629
    | (have j1 := eq612 (σ x) (σ y)
       grind)
    | (have r₁ := eq629
       have r₂ := eq612 y x
       grind)
    | (have r₁ := eq629
       have r₂ := eq612 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq629
       have r₂ := eq612 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq629 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq629
  have eq1064 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1063
  have eq1179 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1064
       grind)
    | exact superpose eq1064 eq8
    | exact resolve eq8 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1215 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1179
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1179
    | exact resolve eq1179 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1216 : x = y := by grind
  clear eq1215
  have eq1343 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1216
       grind)
    | exact superpose eq1216 eq14
    | exact resolve eq14 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1344 : False := by grind
  exact eq1344

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | exact resolve eq32 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq37
    | (have j0 := eq37 (σ (k X0 X1)) (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq37 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq72 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq69 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq69 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq69 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq69 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq151 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq158 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq151 X1 X0
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq151 X0 X1
       have r₂ := eq77 (k X1 X0) (M.op X1 X1)
       grind)
    | (have r₁ := eq151 X0 X1
       have r₂ := eq77 (M.op X1 X1) (k X1 X0)
       grind)
    | exact resolve eq151 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq151
  have eq276 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq72 (τ X1) X0
       grind)
    | exact superpose eq72 eq16
    | (have j1 := eq72 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq72
  have eq575 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq276
    | exact resolve eq276 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq612 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq575 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq575
    | (have j0 := eq575 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq575 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq629 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq158 x y
       grind)
    | exact superpose eq158 eq14
    | (have j1 := eq158 x y
       grind)
    | exact resolve eq14 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq1063 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq629
       have i₂ := eq612 y x
       grind)
    | exact superpose eq612 eq629
    | (have j1 := eq612 (σ x) (σ y)
       grind)
    | (have r₁ := eq629
       have r₂ := eq612 y x
       grind)
    | (have r₁ := eq629
       have r₂ := eq612 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq629
       have r₂ := eq612 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq629 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq629
  have eq1064 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1063
  have eq1179 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1064
       grind)
    | exact superpose eq1064 eq8
    | exact resolve eq8 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1215 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1179
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1179
    | exact resolve eq1179 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1216 : x = y := by grind
  clear eq1215
  have eq1343 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1216
       grind)
    | exact superpose eq1216 eq14
    | exact resolve eq14 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1344 : False := by grind
  exact eq1344

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq38 (σ X0) (σ X1)
       grind)
    | exact superpose eq38 eq13
    | (have j1 := eq38 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq38 (τ X0) X1
       grind)
    | exact superpose eq38 eq16
    | (have j1 := eq38 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq38
  have eq162 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq56
    | exact resolve eq56 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq184 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq162 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq162
    | (have j0 := eq162 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq162 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq558 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq55 x y
       grind)
    | exact superpose eq55 eq14
    | (have j1 := eq55 x y
       grind)
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq578 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq558
       have i₂ := eq184 x y
       grind)
    | exact superpose eq184 eq558
    | (have j1 := eq184 (σ x) (σ y)
       grind)
    | (have r₁ := eq558
       have r₂ := eq184 x y
       grind)
    | (have r₁ := eq558
       have r₂ := eq184 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq558
       have r₂ := eq184 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq558 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq558
  have eq579 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq578
  have eq658 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq579
       grind)
    | exact superpose eq579 eq8
    | exact resolve eq8 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq693 : x = y ∨ x = y := by
    first
    | (have i₁ := eq658
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq658
    | exact resolve eq658 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq694 : x = y := by grind
  clear eq693
  have eq781 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq694
       grind)
    | exact superpose eq694 eq14
    | exact resolve eq14 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq782 : False := by grind
  exact eq782

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq38 (σ X0) (σ X1)
       grind)
    | exact superpose eq38 eq13
    | (have j1 := eq38 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq38 (τ X0) X1
       grind)
    | exact superpose eq38 eq16
    | (have j1 := eq38 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq38
  have eq162 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq56
    | exact resolve eq56 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq184 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq162 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq162
    | (have j0 := eq162 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq162 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq558 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq55 x y
       grind)
    | exact superpose eq55 eq14
    | (have j1 := eq55 x y
       grind)
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq578 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq558
       have i₂ := eq184 x y
       grind)
    | exact superpose eq184 eq558
    | (have j1 := eq184 (σ x) (σ y)
       grind)
    | (have r₁ := eq558
       have r₂ := eq184 x y
       grind)
    | (have r₁ := eq558
       have r₂ := eq184 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq558
       have r₂ := eq184 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq558 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq558
  have eq579 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq578
  have eq658 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq579
       grind)
    | exact superpose eq579 eq8
    | exact resolve eq8 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq693 : x = y ∨ x = y := by
    first
    | (have i₁ := eq658
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq658
    | exact resolve eq658 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq694 : x = y := by grind
  clear eq693
  have eq781 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq694
       grind)
    | exact superpose eq694 eq14
    | exact resolve eq14 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq782 : False := by grind
  exact eq782

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pxx_pxy_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq68 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       have j1 := eq10 X0 X1
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
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       have j1 := eq10 X0 X1
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
  have eq112 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq68 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq68
    | (have j0 := eq68 X0 X1
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
  have eq119 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq112 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq122 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq119 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq119 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq119 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq124 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq122 X0 X1
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq122
    | (have j0 := eq122 X0 X1
       grind)
    | exact resolve eq122 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq122
  have eq167 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq171 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq167 X0 X1
       have j1 := eq124 X0 X1
       grind)
    | (have r₁ := eq167 X0 X1
       have r₂ := eq124 X0 X1
       grind)
    | (have r₁ := eq167 X1 X1
       have r₂ := eq124 X1 X1
       grind)
    | exact resolve eq167 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq167
  have eq190 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq171 (σ X0) (σ X1)
       grind)
    | exact superpose eq171 eq13
    | exact resolve eq13 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq190 X0 X1
       have i₂ := eq171 X0 X1
       grind)
    | exact superpose eq171 eq190
    | exact resolve eq190 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq190
  have eq689 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq197 x y
       grind)
    | exact superpose eq197 eq14
    | (have r₁ := eq14
       have r₂ := eq197 x y
       grind)
    | exact resolve eq14 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq716 : False := by grind
  exact eq716

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pxx_pxy_pyx_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq98 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
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
  have eq194 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq197 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq194 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq194 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq194 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq194 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq194 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq380 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1
       have i₂ := eq197 (σ X1) X0
       grind)
    | (have i₁ := eq26 X0
       have i₂ := eq197 X0 (σ X0)
       grind)
    | exact superpose eq197 eq26
    | (have j1 := eq197 (σ X1) X0
       grind)
    | exact resolve eq26 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4241 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
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
  have eq8987 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq4241 (σ X1) X0
       grind)
    | exact superpose eq4241 eq13
    | (have j1 := eq4241 (σ X1) X0
       grind)
    | exact resolve eq13 eq4241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4241
  have eq9022 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ (M.op X1 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8987 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq8987
    | (have j0 := eq8987 X0 X1
       grind)
    | exact resolve eq8987 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8987
  have eq9069 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9022 X0 X1
       have i₂ := eq8 (M.op X1 X1)
       grind)
    | exact superpose eq8 eq9022
    | (have j0 := eq9022 X0 X1
       grind)
    | exact resolve eq9022 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9022
  have eq12815 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq9069 x y
       grind)
    | exact superpose eq9069 eq14
    | (have j1 := eq9069 x y
       grind)
    | exact resolve eq14 eq9069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9069
  have eq13056 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq12815
       have i₂ := eq197 x y
       grind)
    | exact superpose eq197 eq12815
    | (have j1 := eq197 x y
       grind)
    | exact resolve eq12815 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq12815
  have eq13058 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq13056
  have eq13059 : (M.op x x) = (M.op y y) := by grind
  clear eq13058
  have eq13178 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq13059
       grind)
    | exact superpose eq13059 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq13059
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq13059
       grind)
    | exact resolve eq10 eq13059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13211 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq98 y X0
       have i₂ := eq13059
       grind)
    | exact superpose eq13059 eq98
    | (have j0 := eq98 x X0
       grind)
    | exact resolve eq98 eq13059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq13059
  have eq13424 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq13178 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13178
  have eq27000 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13211 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq13211
    | (have j0 := eq13211 (σ X0)
       grind)
    | (have r₁ := eq13211 (σ x)
       have r₂ := eq26 x
       grind)
    | exact resolve eq13211 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13211
  have eq27024 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq27000 X0
       have i₂ := eq13 y X0
       grind)
    | exact superpose eq13 eq27000
    | (have j0 := eq27000 X0
       grind)
    | exact resolve eq27000 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27000
  have eq572189 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j0 := eq27024 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27024
  have eq572191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq572189
       have i₂ := eq13424
       grind)
    | exact superpose eq13424 eq572189
    | exact resolve eq572189 eq13424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13424 eq572189
  have eq572194 : False := by grind
  exact eq572194

/-- `x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pxx_pyx_pxy_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq99 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq194 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq197 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq194 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq194 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq194 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq194 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq194 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq380 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1
       have i₂ := eq197 (σ X1) X0
       grind)
    | (have i₁ := eq26 X0
       have i₂ := eq197 X0 (σ X0)
       grind)
    | exact superpose eq197 eq26
    | (have j1 := eq197 (σ X1) X0
       grind)
    | exact resolve eq26 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4261 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
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
  have eq9013 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq4261 (σ X0) X1
       grind)
    | exact superpose eq4261 eq13
    | (have j1 := eq4261 (σ X0) X1
       grind)
    | exact resolve eq13 eq4261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4261
  have eq9048 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9013 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq9013
    | (have j0 := eq9013 X0 X1
       grind)
    | exact resolve eq9013 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9013
  have eq9095 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9048 X0 X1
       have i₂ := eq8 (M.op X0 X0)
       grind)
    | exact superpose eq8 eq9048
    | (have j0 := eq9048 X0 X1
       grind)
    | exact resolve eq9048 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9048
  have eq12841 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq9095 x y
       grind)
    | exact superpose eq9095 eq14
    | (have j1 := eq9095 y x
       grind)
    | exact resolve eq14 eq9095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9095
  have eq13085 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq12841
       have i₂ := eq197 y x
       grind)
    | exact superpose eq197 eq12841
    | (have j1 := eq197 y x
       grind)
    | exact resolve eq12841 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq12841
  have eq13090 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq13085
  have eq13091 : (M.op y y) = (M.op x x) := by grind
  clear eq13090
  have eq13215 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq13091
       grind)
    | exact superpose eq13091 eq10
    | (have j0 := eq10 X0 x
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq13091
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq13091
       grind)
    | exact resolve eq10 eq13091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13248 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq99 y X0
       have i₂ := eq13091
       grind)
    | exact superpose eq13091 eq99
    | (have j0 := eq99 x X0
       grind)
    | exact resolve eq99 eq13091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq13091
  have eq14628 : (M.op x y) = (k x y) := by
    first
    | (have j0 := eq13215 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13215
  have eq29964 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13248 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq13248
    | (have j0 := eq13248 (σ X0)
       grind)
    | (have r₁ := eq13248 (σ x)
       have r₂ := eq26 x
       grind)
    | exact resolve eq13248 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13248
  have eq29988 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq29964 X0
       have i₂ := eq13 X0 y
       grind)
    | exact superpose eq13 eq29964
    | (have j0 := eq29964 X0
       grind)
    | exact resolve eq29964 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29964
  have eq609409 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have j0 := eq29988 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29988
  have eq609411 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq609409
       have i₂ := eq14628
       grind)
    | exact superpose eq14628 eq609409
    | exact resolve eq609409 eq14628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14628 eq609409
  have eq609414 : False := by grind
  exact eq609414

/-- `x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyy_pxx_pyx_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq68 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       have j1 := eq10 X0 X1
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
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       have j1 := eq10 X0 X1
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
  have eq112 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq68 X0 X1
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
  have eq119 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq112 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq122 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq119 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq119 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq119 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq124 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq122 X0 X1
       have i₂ := eq21 X1
       grind)
    | exact superpose eq21 eq122
    | (have j0 := eq122 X0 X1
       grind)
    | exact resolve eq122 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq122
  have eq167 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq171 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq167 X0 X1
       have j1 := eq124 X1 X0
       grind)
    | (have r₁ := eq167 X1 X0
       have r₂ := eq124 X0 X1
       grind)
    | (have r₁ := eq167 X1 X1
       have r₂ := eq124 X1 X1
       grind)
    | exact resolve eq167 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq167
  have eq189 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq171 (σ X1) (σ X0)
       grind)
    | exact superpose eq171 eq13
    | exact resolve eq13 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 X1
       have i₂ := eq171 X1 X0
       grind)
    | exact superpose eq171 eq189
    | exact resolve eq189 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq189
  have eq694 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq196 x y
       grind)
    | exact superpose eq196 eq14
    | (have r₁ := eq14
       have r₂ := eq196 x y
       grind)
    | exact resolve eq14 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq721 : False := by grind
  exact eq721
