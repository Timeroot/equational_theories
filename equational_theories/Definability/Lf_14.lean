import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyy_x_y_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq57 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq39 (σ X0) (σ X1)
       grind)
    | exact superpose eq39 eq13
    | (have j1 := eq39 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq13 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq39 X0 (τ X1)
       grind)
    | exact superpose eq39 eq16
    | (have j1 := eq39 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq39
  have eq205 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq58
    | exact resolve eq58 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq227 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq205
    | (have j0 := eq205 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq205 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq584 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq57 x y
       grind)
    | exact superpose eq57 eq14
    | (have j1 := eq57 x y
       grind)
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq686 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq584
       have i₂ := eq227 y x
       grind)
    | exact superpose eq227 eq584
    | (have j1 := eq227 (σ x) (σ y)
       grind)
    | (have r₁ := eq584
       have r₂ := eq227 y x
       grind)
    | (have r₁ := eq584
       have r₂ := eq227 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq584
       have r₂ := eq227 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq584 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq584
  have eq687 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq686
  have eq780 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq687
       grind)
    | exact superpose eq687 eq8
    | exact resolve eq8 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq815 : x = y ∨ x = y := by
    first
    | (have i₁ := eq780
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq780
    | exact resolve eq780 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq816 : x = y := by grind
  clear eq815
  have eq995 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq816
       grind)
    | exact superpose eq816 eq14
    | exact resolve eq14 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq996 : False := by grind
  exact eq996

/-- `x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyy_x_y_pyy_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq32 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq38
    | (have j0 := eq38 (σ (k X0 X1)) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq38 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq72 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
       have r₂ := eq12 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq69 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq152 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq160 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq152 X0 X1
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq152 X0 X1
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq152 X0 X1
       have r₂ := eq77 (k X0 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq152 X0 X1
       have r₂ := eq77 (M.op X1 X1) (k X0 X1)
       grind)
    | exact resolve eq152 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq152
  have eq276 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq72 (τ X0) X1
       grind)
    | exact superpose eq72 eq16
    | (have j1 := eq72 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq72
  have eq576 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq276 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq276
    | exact resolve eq276 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq613 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq576 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq576
    | (have j0 := eq576 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq576 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq630 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
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
  have eq1083 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq630
       have i₂ := eq613 x y
       grind)
    | exact superpose eq613 eq630
    | (have j1 := eq613 (σ x) (σ y)
       grind)
    | (have r₁ := eq630
       have r₂ := eq613 x y
       grind)
    | (have r₁ := eq630
       have r₂ := eq613 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq630
       have r₂ := eq613 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq630 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq630
  have eq1084 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1083
  have eq1199 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1084
       grind)
    | exact superpose eq1084 eq8
    | exact resolve eq8 eq1084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1234 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1199
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1199
    | exact resolve eq1199 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1235 : x = y := by grind
  clear eq1234
  have eq1366 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1235
       grind)
    | exact superpose eq1235 eq14
    | exact resolve eq14 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq1367 : False := by grind
  exact eq1367

/-- `x □ y = if m(X,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_x_pxx_pxy_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq51 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq51 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq54 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | (have r₁ := eq54 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq64 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq59 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq59 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq59
  have eq160 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq165 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq160 X0 X1
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq160 X0 X1
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq160 X1 X1
       have r₂ := eq63 X1 X1
       grind)
    | exact resolve eq160 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq160
  have eq186 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq165 (σ X0) (σ X1)
       grind)
    | exact superpose eq165 eq13
    | exact resolve eq13 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 X1
       have i₂ := eq165 X0 X1
       grind)
    | exact superpose eq165 eq186
    | exact resolve eq186 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq186
  have eq1441 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq195 x y
       grind)
    | exact superpose eq195 eq14
    | (have r₁ := eq14
       have r₂ := eq195 x y
       grind)
    | exact resolve eq14 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq1462 : False := by grind
  exact eq1462

/-- `x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_x_pxx_pyx_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 (M.op X0 X0) X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq49 (k X1 X1) X1
       have r₂ := eq10 (k X1 X1) X1
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
    | (have r₁ := eq51 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | (have r₁ := eq51 (k X1 X1) X1
       have r₂ := eq10 (k X1 X1) X1
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

/-- `x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_x_pxy_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq74 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq79 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       have j1 := eq10 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq74 X0 X1
       have r₂ := eq10 (σ X0) (σ X1)
       grind)
    | exact resolve eq74 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq128 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq86
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq86 x y
       grind)
    | exact superpose eq86 eq14
    | exact resolve eq14 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq333 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X0)
       have i₂ := eq128 X0 (τ X1)
       grind)
    | exact superpose eq128 eq16
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq128
  have eq358 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
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
  have eq370 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq358 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq358
    | exact resolve eq358 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq532 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq139
       have i₂ := eq370 x y
       grind)
    | exact superpose eq370 eq139
    | exact resolve eq139 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq370
  have eq533 : False := by grind
  exact eq533

/-- `x □ y = if m(X,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_x_pxy_pyx_pyx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq42 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq66 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq42 X0 X1
       grind)
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq10
    | (have j0 := eq10 (σ X1) (σ X0)
       have j1 := eq42 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
       have r₂ := eq42 X0 X1
       grind)
    | exact resolve eq10 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq75 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq80 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       have j1 := eq10 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq66 X0 X1
       have r₂ := eq10 (σ X1) (σ X0)
       grind)
    | exact resolve eq66 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq81 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       have j1 := eq10 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq75 X1 X1
       have r₂ := eq10 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq75 X0 X1
       have r₂ := eq10 (σ X1) (σ X0)
       grind)
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq80
    | (have j0 := eq80 X0 X1
       grind)
    | exact resolve eq80 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq90 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq91 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq90 X0 X1
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq90 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq90
  have eq131 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
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
  have eq142 : (σ (M.op x y)) ≠ (σ (k y x)) := by
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
  have eq336 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq131 X0 (τ X1)
       grind)
    | exact superpose eq131 eq15
    | exact resolve eq15 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq131
  have eq362 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq336
    | exact resolve eq336 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq374 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
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
  have eq532 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq533 : False := by grind
  exact eq533

/-- `x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_x_pxy_pyy_pxy_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
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
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq51 (k X1 X1) X1
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq49 (k X1 X1) X1
       have r₂ := eq10 (k X1 X1) X1
       grind)
    | (have r₁ := eq49 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq52 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | (have r₁ := eq52 (k X1 X1) X1
       have r₂ := eq10 (k X1 X1) X1
       grind)
    | (have r₁ := eq52 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq52 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq53 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | (have r₁ := eq53 X0 (M.op (M.op X0 X0) X1)
       have r₂ := eq10 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq53 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq65 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq122 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X1 X0
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
    | (have r₁ := eq122 X0 X0
       have r₂ := eq67 X0 X0
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
  have eq1053 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
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
  have eq1076 : False := by grind
  exact eq1076

/-- `x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_x_pxy_y_pxy_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = b :=
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq61 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq294 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (τ X0) (τ X1)
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq64
    | (have j0 := eq64 (τ X0) (τ X1)
       grind)
    | exact resolve eq64 eq29
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
    | (have i₁ := eq65 (τ X0) (τ X1)
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq65
    | (have j0 := eq65 (τ X0) (τ X1)
       grind)
    | exact resolve eq65 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
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
    | (have i₁ := eq61
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq61
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq61 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq415 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq414
  have eq2756 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq2758 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq415
  have eq2759 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2756
  have eq2760 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2759
       have r₂ := eq2758
       grind)
    | exact resolve eq2759 eq2758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2758 eq2759
  have eq2762 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2760
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq2760
    | exact resolve eq2760 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2760
  have eq19228 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ x) (σ y)
       have i₂ := eq2762
       grind)
    | exact superpose eq2762 eq10
    | (have r₁ := eq10 (σ x) (σ y)
       have r₂ := eq2762
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq2762
       grind)
    | exact resolve eq10 eq2762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2762
  have eq19229 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19228
  have eq19231 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19229
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq19229
    | exact resolve eq19229 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19229
  have eq19708 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq19231
       grind)
    | exact superpose eq19231 eq8
    | exact resolve eq8 eq19231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19231
  have eq19855 : y = (k x y) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19708
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq19708
    | exact resolve eq19708 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19708
  have eq19858 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq309 x y
       grind)
    | (have r₁ := eq19855
       have r₂ := eq309 x y
       grind)
    | exact resolve eq19855 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq19855
  have eq20103 : (k x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8 (k x y)
       have i₂ := eq19858
       grind)
    | exact superpose eq19858 eq8
    | exact resolve eq8 eq19858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19858
  have eq20250 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20103
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq20103
    | exact resolve eq20103 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20103
  have eq20251 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq369 x y
       grind)
    | (have r₁ := eq20250
       have r₂ := eq369 x y
       grind)
    | exact resolve eq20250 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq20250
  have eq20480 : y ≠ y ∨ x = y ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq20251
       grind)
    | exact superpose eq20251 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq20251
       grind)
    | exact resolve eq11 eq20251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20482 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq20483 : x = y ∨ y = (k x y) ∨ x = (M.op x y) := by grind
  clear eq20480
  have eq20484 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20483
       have r₂ := eq20482
       grind)
    | exact resolve eq20483 eq20482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20483
  have eq21001 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64 x y
       have i₂ := eq20484
       grind)
    | exact superpose eq20484 eq64
    | (have j0 := eq64 x y
       grind)
    | exact resolve eq64 eq20484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq21046 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21001
  have eq26240 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21046
       grind)
    | exact superpose eq21046 eq14
    | exact resolve eq14 eq21046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21046
  have eq26918 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26240
       have i₂ := eq20251
       grind)
    | exact superpose eq20251 eq26240
    | exact resolve eq26240 eq20251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26240
  have eq26921 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq26918
  have eq26922 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26921
       have r₂ := eq20482
       grind)
    | exact resolve eq26921 eq20482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26921
  have eq27342 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq26922
       grind)
    | exact superpose eq26922 eq14
    | exact resolve eq14 eq26922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27343 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ x) (σ y)
       have i₂ := eq26922
       grind)
    | exact superpose eq26922 eq10
    | (have r₁ := eq10 (σ x) (σ y)
       have r₂ := eq26922
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq26922
       grind)
    | exact resolve eq10 eq26922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26922
  have eq27344 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27343
  have eq27347 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27344
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq27344
    | exact resolve eq27344 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27344
  have eq27720 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27342
       have i₂ := eq20251
       grind)
    | exact superpose eq20251 eq27342
    | exact resolve eq27342 eq20251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20251 eq27342
  have eq27724 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27720
       have r₂ := eq20482
       grind)
    | exact resolve eq27720 eq20482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20482 eq27720
  have eq28417 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27347
       have i₂ := eq20484
       grind)
    | exact superpose eq20484 eq27347
    | exact resolve eq27347 eq20484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20484 eq27347
  have eq28569 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq28417
  have eq28628 : x = (M.op x y) := by
    first
    | (have r₁ := eq28569
       have r₂ := eq27724
       grind)
    | exact resolve eq28569 eq27724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27724 eq28569
  have eq28958 : x ≠ x ∨ x = (k x y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq28628
       grind)
    | exact superpose eq28628 eq10
    | (have r₁ := eq10 x y
       have r₂ := eq28628
       grind)
    | exact resolve eq10 eq28628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28959 : x = (k x y) := by grind
  clear eq28958
  have eq29346 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65 x y
       have i₂ := eq28959
       grind)
    | exact superpose eq28959 eq65
    | (have j0 := eq65 x y
       grind)
    | exact resolve eq65 eq28959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq29372 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29346
  have eq32410 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq29372
       grind)
    | exact superpose eq29372 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq29372
       grind)
    | exact resolve eq11 eq29372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32412 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29372
  have eq32413 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq32410
  have eq32414 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq32413
       have r₂ := eq32412
       grind)
    | exact resolve eq32413 eq32412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32413
  have eq32417 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32414
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq32414
    | exact resolve eq32414 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32414
  have eq32419 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32417
       have i₂ := eq28959
       grind)
    | exact superpose eq28959 eq32417
    | exact resolve eq32417 eq28959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28959 eq32417
  have eq32420 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq32419
       have r₂ := eq32412
       grind)
    | exact resolve eq32419 eq32412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32412 eq32419
  have eq32681 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq32420
       grind)
    | exact superpose eq32420 eq14
    | exact resolve eq14 eq32420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32420
  have eq32685 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq32681
       have i₂ := eq28628
       grind)
    | exact superpose eq28628 eq32681
    | exact resolve eq32681 eq28628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28628 eq32681
  have eq32686 : False := by grind
  exact eq32686
