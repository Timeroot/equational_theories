import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyx_pxy_pyy_pxy_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq52 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq52 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq52 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq53 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq55 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | (have r₁ := eq55 X0 X0
       have r₂ := eq10 X0 X0
       grind)
    | (have r₁ := eq55 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq55 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq21 X1
       grind)
    | exact superpose eq21 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq58
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       have j1 := eq56 X1 X0
       grind)
    | (have r₁ := eq62 X1 X0
       have r₂ := eq56 X0 X1
       grind)
    | (have r₁ := eq62 X0 X0
       have r₂ := eq56 X0 X0
       grind)
    | exact resolve eq62 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq62
  have eq179 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq68 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq186 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq179 X0 X1
       have j1 := eq66 X0 X1
       grind)
    | (have r₁ := eq179 X0 X1
       have r₂ := eq66 X0 X1
       grind)
    | (have r₁ := eq179 X0 X0
       have r₂ := eq66 X0 X0
       grind)
    | exact resolve eq179 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq179
  have eq212 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq186 (σ X0) (σ X1)
       grind)
    | exact superpose eq186 eq13
    | exact resolve eq13 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 X1
       have i₂ := eq186 X0 X1
       grind)
    | exact superpose eq186 eq212
    | exact resolve eq212 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq212
  have eq1556 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq219 x y
       grind)
    | exact superpose eq219 eq14
    | (have r₁ := eq14
       have r₂ := eq219 x y
       grind)
    | exact resolve eq14 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq1579 : False := by grind
  exact eq1579

/-- `x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyx_pxy_x_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq41 X0 X1
       grind)
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq10
    | (have j0 := eq10 (σ X0) (σ X1)
       have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
       have r₂ := eq41 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq10 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq70 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq263 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq75 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq75
    | exact resolve eq75 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq14
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq14 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq10
    | (have j0 := eq10 (σ X1) (σ X0)
       have j1 := eq75 X0 X1
       grind)
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq278 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq278
    | (have j0 := eq278 X0 X1
       grind)
    | exact resolve eq278 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq285 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq263 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq263
    | (have j0 := eq263 X0 X1
       grind)
    | exact resolve eq263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq263
  have eq1286 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq285 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq285
    | exact resolve eq285 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq1353 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq1286 (τ X1) X0
       grind)
    | exact superpose eq1286 eq16
    | (have j1 := eq1286 (τ X1) X0
       grind)
    | exact resolve eq16 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq1456 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq274
       have i₂ := eq1286 y x
       grind)
    | exact superpose eq1286 eq274
    | (have j1 := eq1286 (σ y) (σ x)
       grind)
    | exact resolve eq274 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1459 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1456
  have eq1462 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1459
       grind)
    | exact superpose eq1459 eq14
    | exact resolve eq14 eq1459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1465 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq1459
       grind)
    | exact superpose eq1459 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq1459
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq1459
       grind)
    | exact resolve eq11 eq1459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1466 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1465
  have eq1467 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1466
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1466
    | exact resolve eq1466 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq2281 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1353 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq1353
    | exact resolve eq1353 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq2344 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2281 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2281
    | (have j0 := eq2281 X0 X1
       grind)
    | exact resolve eq2281 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2281
  have eq7527 : (σ x) ≠ (σ (k y x)) ∨ (σ x) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq281 y x
       have i₂ := eq1459
       grind)
    | exact superpose eq1459 eq281
    | (have j0 := eq281 y x
       grind)
    | exact resolve eq281 eq1459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq1459
  have eq16475 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1467
       have i₂ := eq75 y x
       grind)
    | exact superpose eq75 eq1467
    | (have j1 := eq75 y x
       grind)
    | exact resolve eq1467 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq16523 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq16475
       have r₂ := eq7527
       grind)
    | exact resolve eq16475 eq7527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7527 eq16475
  have eq27235 : (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq1467
       have i₂ := eq16523
       grind)
    | exact superpose eq16523 eq1467
    | exact resolve eq1467 eq16523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467 eq16523
  have eq27244 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq27235
  have eq27660 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2344 y x
       have i₂ := eq27244
       grind)
    | exact superpose eq27244 eq2344
    | (have j0 := eq2344 y x
       grind)
    | exact resolve eq2344 eq27244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344 eq27244
  have eq27757 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq27660
  have eq27785 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq27757
       have r₂ := eq1462
       grind)
    | exact resolve eq27757 eq1462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462 eq27757
  have eq28142 : x ≠ x ∨ x = (M.op y x) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq27785
       grind)
    | exact superpose eq27785 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq27785
       grind)
    | exact resolve eq11 eq27785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28143 : x = (k x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq28142
  have eq28503 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq280 x y
       have i₂ := eq28143
       grind)
    | exact superpose eq28143 eq280
    | (have j0 := eq280 x y
       grind)
    | exact resolve eq280 eq28143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq28143
  have eq28532 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq28503
  have eq29315 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq28532
       grind)
    | exact superpose eq28532 eq14
    | exact resolve eq14 eq28532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28532
  have eq29691 : (σ x) ≠ (σ x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29315
       have i₂ := eq27785
       grind)
    | exact superpose eq27785 eq29315
    | exact resolve eq29315 eq27785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29315
  have eq29692 : (σ x) ≠ (σ x) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq29691
  have eq29693 : x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq29692
  have eq30070 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq29693
       grind)
    | exact superpose eq29693 eq10
    | (have j0 := eq10 x y
       grind)
    | exact resolve eq10 eq29693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29693
  have eq30073 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq1286 y x
       grind)
    | (have r₁ := eq30070
       have r₂ := eq1286 y x
       grind)
    | exact resolve eq30070 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286 eq30070
  have eq30920 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq274
       have i₂ := eq30073
       grind)
    | exact superpose eq30073 eq274
    | exact resolve eq274 eq30073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq30073
  have eq30926 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq30920
  have eq31790 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30926
       grind)
    | exact superpose eq30926 eq14
    | exact resolve eq14 eq30926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30926
  have eq32237 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq31790
       have i₂ := eq27785
       grind)
    | exact superpose eq27785 eq31790
    | exact resolve eq31790 eq27785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27785 eq31790
  have eq32238 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq32237
  have eq32239 : (σ x) = (σ y) := by grind
  clear eq32238
  have eq32647 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq32239
       grind)
    | exact superpose eq32239 eq14
    | exact resolve eq14 eq32239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32654 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq32239
       grind)
    | exact superpose eq32239 eq8
    | exact resolve eq8 eq32239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32239
  have eq32766 : x = y := by
    first
    | (have i₁ := eq32654
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq32654
    | exact resolve eq32654 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32654
  have eq32772 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq32647
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq32647
    | exact resolve eq32647 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq32647
  have eq32778 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq32772
       have i₂ := eq32766
       grind)
    | exact superpose eq32766 eq32772
    | exact resolve eq32772 eq32766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32766 eq32772
  have eq32779 : False := by grind
  exact eq32779

/-- `x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyx_pxy_y_pxy_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq41 X0 X1
       grind)
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq10
    | (have j0 := eq10 (σ X0) (σ X1)
       have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
       have r₂ := eq41 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq10 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq70 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq267 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq75
    | exact resolve eq75 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq14
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq14 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq10
    | (have j0 := eq10 (σ X1) (σ X0)
       have j1 := eq75 X0 X1
       grind)
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq278 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq278
    | (have j0 := eq278 X0 X1
       grind)
    | exact resolve eq278 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq283 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq267 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq267
    | (have j0 := eq267 X0 X1
       grind)
    | exact resolve eq267 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq267
  have eq1287 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq283 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq283
    | exact resolve eq283 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq1370 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1287 (τ X0) X1
       grind)
    | exact superpose eq1287 eq15
    | (have j1 := eq1287 (τ X0) X1
       grind)
    | exact resolve eq15 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq1457 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq274
       have i₂ := eq1287 x y
       grind)
    | exact superpose eq1287 eq274
    | (have j1 := eq1287 (σ x) (σ y)
       grind)
    | exact resolve eq274 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1460 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1457
  have eq1463 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1460
       grind)
    | exact superpose eq1460 eq14
    | exact resolve eq14 eq1460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1466 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq1460
       grind)
    | exact superpose eq1460 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq1460
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq1460
       grind)
    | exact resolve eq11 eq1460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1467 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1466
  have eq1468 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1467
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq1467
    | exact resolve eq1467 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq2133 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1370 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq1370
    | exact resolve eq1370 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq2196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2133 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2133
    | (have j0 := eq2133 X0 X1
       grind)
    | exact resolve eq2133 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133
  have eq7521 : (σ y) ≠ (σ (k y x)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq281 y x
       have i₂ := eq1460
       grind)
    | exact superpose eq1460 eq281
    | (have j0 := eq281 y x
       grind)
    | exact resolve eq281 eq1460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq1460
  have eq16075 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1468
       have i₂ := eq75 y x
       grind)
    | exact superpose eq75 eq1468
    | (have j1 := eq75 y x
       grind)
    | exact resolve eq1468 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq16123 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq16075
       have r₂ := eq7521
       grind)
    | exact resolve eq16075 eq7521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7521 eq16075
  have eq24377 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq1468
       have i₂ := eq16123
       grind)
    | exact superpose eq16123 eq1468
    | exact resolve eq1468 eq16123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468 eq16123
  have eq24386 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq24377
  have eq24751 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2196 x y
       have i₂ := eq24386
       grind)
    | exact superpose eq24386 eq2196
    | (have j0 := eq2196 x y
       grind)
    | exact resolve eq2196 eq24386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2196 eq24386
  have eq24831 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq24751
  have eq24859 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq24831
       have r₂ := eq1463
       grind)
    | exact resolve eq24831 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463 eq24831
  have eq25211 : y ≠ y ∨ y = (M.op y x) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq24859
       grind)
    | exact superpose eq24859 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq24859
       grind)
    | exact resolve eq11 eq24859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25212 : y = (k x y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq25211
  have eq25597 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq280 x y
       have i₂ := eq25212
       grind)
    | exact superpose eq25212 eq280
    | (have j0 := eq280 x y
       grind)
    | exact resolve eq280 eq25212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq25212
  have eq25626 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq25597
  have eq26383 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq25626
       grind)
    | exact superpose eq25626 eq14
    | exact resolve eq14 eq25626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25626
  have eq26750 : (σ y) ≠ (σ y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26383
       have i₂ := eq24859
       grind)
    | exact superpose eq24859 eq26383
    | exact resolve eq26383 eq24859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26383
  have eq26751 : (σ y) ≠ (σ y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq26750
  have eq26752 : y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq26751
  have eq27152 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq26752
       grind)
    | exact superpose eq26752 eq10
    | (have j0 := eq10 x y
       grind)
    | exact resolve eq10 eq26752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26752
  have eq27155 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq1287 x y
       grind)
    | (have r₁ := eq27152
       have r₂ := eq1287 x y
       grind)
    | exact resolve eq27152 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287 eq27152
  have eq27945 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq274
       have i₂ := eq27155
       grind)
    | exact superpose eq27155 eq274
    | exact resolve eq274 eq27155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq27155
  have eq27951 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq27945
  have eq28694 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq27951
       grind)
    | exact superpose eq27951 eq14
    | exact resolve eq14 eq27951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27951
  have eq29089 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28694
       have i₂ := eq24859
       grind)
    | exact superpose eq24859 eq28694
    | exact resolve eq28694 eq24859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24859 eq28694
  have eq29090 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq29089
  have eq29091 : (σ x) = (σ y) := by grind
  clear eq29090
  have eq29481 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29091
       grind)
    | exact superpose eq29091 eq14
    | exact resolve eq14 eq29091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29487 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq29091
       grind)
    | exact superpose eq29091 eq8
    | exact resolve eq8 eq29091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29091
  have eq29612 : x = y := by
    first
    | (have i₁ := eq29487
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq29487
    | exact resolve eq29487 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29487
  have eq29618 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq29481
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq29481
    | exact resolve eq29481 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq29481
  have eq29624 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq29618
       have i₂ := eq29612
       grind)
    | exact superpose eq29612 eq29618
    | exact resolve eq29618 eq29612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29612 eq29618
  have eq29625 : False := by grind
  exact eq29625

/-- `x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyx_pyx_pyy_pxy_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       have j1 := eq52 X0 X1
       grind)
    | (have r₁ := eq55 X0 X1
       have r₂ := eq52 X0 X1
       grind)
    | (have r₁ := eq55 X1 X1
       have r₂ := eq52 X1 X1
       grind)
    | (have r₁ := eq55 X0 X0
       have r₂ := eq52 X0 X0
       grind)
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq55
  have eq60 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq122 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq59
    | (have j0 := eq59 (σ X1) (σ X0)
       grind)
    | exact resolve eq59 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq148 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq142 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq142 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq142 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq142 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq159 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq122 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq122
    | (have j0 := eq122 X0 X1
       grind)
    | exact resolve eq122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq122
  have eq235 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq242 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq235 X0 X1
       have j1 := eq159 X1 X0
       grind)
    | (have r₁ := eq235 X1 X0
       have r₂ := eq159 X0 X1
       grind)
    | exact resolve eq235 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq235
  have eq850 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq242 X0 X1
       grind)
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq242 X0 X1
       grind)
    | exact superpose eq242 eq10
    | (have j1 := eq242 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
       have r₂ := eq242 X0 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
       have r₂ := eq242 X0 X1
       grind)
    | exact resolve eq10 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq864 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq850 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq871 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq864 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq864
    | (have j0 := eq864 X0 X1
       grind)
    | exact resolve eq864 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq872 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq871 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq914 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq872 x y
       grind)
    | exact superpose eq872 eq14
    | exact resolve eq14 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq1055 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq914
       have i₂ := eq148 y x
       grind)
    | exact superpose eq148 eq914
    | (have j1 := eq148 x y
       grind)
    | exact resolve eq914 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq1064 : (M.op x y) = (M.op y x) := by grind
  clear eq1055
  have eq1183 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq1064
       grind)
    | exact superpose eq1064 eq10
    | (have r₁ := eq10 x y
       have r₂ := eq1064
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq1064
       grind)
    | exact resolve eq10 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1188 : (M.op x y) = (k y x) := by grind
  clear eq1183
  have eq1329 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq914
       have i₂ := eq1188
       grind)
    | exact superpose eq1188 eq914
    | exact resolve eq914 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq1188
  have eq1330 : False := by grind
  exact eq1330

/-- `x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyx_pyx_x_pxy_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq41 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq41 X0 X1
       grind)
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq10
    | (have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
       have r₂ := eq41 X0 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq10 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq71 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq76 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq268 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq14
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq14 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq285 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq268
    | (have j0 := eq268 X0 X1
       grind)
    | exact resolve eq268 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq268
  have eq1292 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq285 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq285
    | exact resolve eq285 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq1359 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq1292 (τ X0) X1
       grind)
    | exact superpose eq1292 eq16
    | (have j1 := eq1292 (τ X0) X1
       grind)
    | exact resolve eq16 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq1462 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq275
       have i₂ := eq1292 x y
       grind)
    | exact superpose eq1292 eq275
    | (have j1 := eq1292 (σ x) (σ y)
       grind)
    | exact resolve eq275 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq1292
  have eq1465 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1462
  have eq1467 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1465
       grind)
    | exact superpose eq1465 eq14
    | exact resolve eq14 eq1465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1470 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq1465
       grind)
    | exact superpose eq1465 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq1465
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq1465
       grind)
    | exact resolve eq11 eq1465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1471 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1470
  have eq1472 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1471
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq1471
    | exact resolve eq1471 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471
  have eq2286 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1359 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq1359
    | exact resolve eq1359 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359
  have eq2349 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2286 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2286
    | (have j0 := eq2286 X0 X1
       grind)
    | exact resolve eq2286 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2286
  have eq15775 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq1472
       grind)
    | exact superpose eq1472 eq10
    | exact resolve eq10 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq15779 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15775
       have r₂ := eq1465
       grind)
    | exact resolve eq15775 eq1465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465 eq15775
  have eq15797 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15779
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq15779
    | exact resolve eq15779 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15779
  have eq15798 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq15797
  have eq16087 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2349 x y
       have i₂ := eq15798
       grind)
    | exact superpose eq15798 eq2349
    | (have j0 := eq2349 x y
       grind)
    | exact resolve eq2349 eq15798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2349 eq15798
  have eq16149 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq16087
  have eq16178 : y = (M.op x y) := by
    first
    | (have r₁ := eq16149
       have r₂ := eq1467
       grind)
    | exact resolve eq16149 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467 eq16149
  have eq16426 : y ≠ y ∨ y = (M.op y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq16178
       grind)
    | exact superpose eq16178 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq16178
       grind)
    | exact resolve eq11 eq16178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16427 : y = (k y x) ∨ y = (M.op y x) := by grind
  clear eq16426
  have eq16730 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq281 x y
       have i₂ := eq16427
       grind)
    | exact superpose eq16427 eq281
    | (have j0 := eq281 x y
       grind)
    | exact resolve eq281 eq16427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16427
  have eq16756 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq16730
  have eq17103 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq16756
       grind)
    | exact superpose eq16756 eq14
    | exact resolve eq14 eq16756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16756
  have eq17110 : (σ y) ≠ (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq17103
       have i₂ := eq16178
       grind)
    | exact superpose eq16178 eq17103
    | exact resolve eq17103 eq16178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17103
  have eq17111 : y = (M.op y x) := by grind
  clear eq17110
  have eq17400 : y ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq17111
       grind)
    | exact superpose eq17111 eq10
    | exact resolve eq10 eq17111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17111
  have eq17401 : y = (k y x) := by
    first
    | (have r₁ := eq17400
       have r₂ := eq16178
       grind)
    | exact resolve eq17400 eq16178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17400
  have eq17650 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq281 x y
       have i₂ := eq17401
       grind)
    | exact superpose eq17401 eq281
    | (have j0 := eq281 x y
       grind)
    | exact resolve eq281 eq17401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq17401
  have eq17676 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17650
  have eq18620 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17676
       grind)
    | exact superpose eq17676 eq14
    | exact resolve eq14 eq17676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17676
  have eq18629 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq18620
       have i₂ := eq16178
       grind)
    | exact superpose eq16178 eq18620
    | exact resolve eq18620 eq16178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16178 eq18620
  have eq18630 : False := by grind
  exact eq18630

/-- `x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyx_pyx_y_pxy_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq41 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq41 X0 X1
       grind)
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq10
    | (have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
       have r₂ := eq41 X0 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq10 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq71 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq76 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq264 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq76 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq14
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq14 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq287 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq264 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq264
    | (have j0 := eq264 X0 X1
       grind)
    | exact resolve eq264 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq264
  have eq1293 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq287 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq287
    | exact resolve eq287 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq1376 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1293 (τ X1) X0
       grind)
    | exact superpose eq1293 eq15
    | (have j1 := eq1293 (τ X1) X0
       grind)
    | exact resolve eq15 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq1463 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq275
       have i₂ := eq1293 y x
       grind)
    | exact superpose eq1293 eq275
    | (have j1 := eq1293 (σ y) (σ x)
       grind)
    | exact resolve eq275 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq1293
  have eq1466 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1463
  have eq1468 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1466
       grind)
    | exact superpose eq1466 eq14
    | exact resolve eq14 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1471 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq1466
       grind)
    | exact superpose eq1466 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq1466
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq1466
       grind)
    | exact resolve eq11 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1472 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1471
  have eq1473 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1472
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq1472
    | exact resolve eq1472 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq2138 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1376 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq1376
    | exact resolve eq1376 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq2201 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2138 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2138
    | (have j0 := eq2138 X0 X1
       grind)
    | exact resolve eq2138 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2138
  have eq15377 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq1473
       grind)
    | exact superpose eq1473 eq10
    | exact resolve eq10 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq15381 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15377
       have r₂ := eq1466
       grind)
    | exact resolve eq15377 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466 eq15377
  have eq15399 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15381
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq15381
    | exact resolve eq15381 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15381
  have eq15400 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq15399
  have eq15611 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2201 y x
       have i₂ := eq15400
       grind)
    | exact superpose eq15400 eq2201
    | (have j0 := eq2201 y x
       grind)
    | exact resolve eq2201 eq15400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201 eq15400
  have eq15673 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq15611
  have eq15702 : x = (M.op x y) := by
    first
    | (have r₁ := eq15673
       have r₂ := eq1468
       grind)
    | exact resolve eq15673 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468 eq15673
  have eq15998 : x ≠ x ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq15702
       grind)
    | exact superpose eq15702 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq15702
       grind)
    | exact resolve eq11 eq15702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15999 : x = (k y x) ∨ x = (M.op y x) := by grind
  clear eq15998
  have eq16236 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq281 x y
       have i₂ := eq15999
       grind)
    | exact superpose eq15999 eq281
    | (have j0 := eq281 x y
       grind)
    | exact resolve eq281 eq15999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15999
  have eq16262 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq16236
  have eq16791 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq16262
       grind)
    | exact superpose eq16262 eq14
    | exact resolve eq14 eq16262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16262
  have eq16798 : (σ x) ≠ (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16791
       have i₂ := eq15702
       grind)
    | exact superpose eq15702 eq16791
    | exact resolve eq16791 eq15702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16791
  have eq16799 : x = (M.op y x) := by grind
  clear eq16798
  have eq16907 : x ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq16799
       grind)
    | exact superpose eq16799 eq10
    | exact resolve eq10 eq16799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16799
  have eq16908 : x = (k y x) := by
    first
    | (have r₁ := eq16907
       have r₂ := eq15702
       grind)
    | exact resolve eq16907 eq15702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16907
  have eq17210 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq281 x y
       have i₂ := eq16908
       grind)
    | exact superpose eq16908 eq281
    | (have j0 := eq281 x y
       grind)
    | exact resolve eq281 eq16908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq16908
  have eq17236 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17210
  have eq18037 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq17236
       grind)
    | exact superpose eq17236 eq14
    | exact resolve eq14 eq17236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17236
  have eq18046 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq18037
       have i₂ := eq15702
       grind)
    | exact superpose eq15702 eq18037
    | exact resolve eq18037 eq15702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15702 eq18037
  have eq18047 : False := by grind
  exact eq18047

/-- `x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq31 X0 X1
       grind)
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq10
    | (have j0 := eq10 (σ X0) (σ X1)
       have j1 := eq31 X0 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
       have r₂ := eq31 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq10 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq57 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq267 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq62 x y
       grind)
    | exact superpose eq62 eq14
    | (have j1 := eq62 x y
       grind)
    | exact resolve eq14 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq282 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq267 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq267
    | (have j0 := eq267 X0 X1
       grind)
    | exact resolve eq267 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq267
  have eq314 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq282 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq282
    | exact resolve eq282 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq500 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq273
       have i₂ := eq314 x y
       grind)
    | exact superpose eq314 eq273
    | (have j1 := eq314 (σ x) (σ y)
       grind)
    | (have r₁ := eq273
       have r₂ := eq314 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq273
       have r₂ := eq314 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq273 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq314
  have eq503 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq500
  have eq566 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq503
       grind)
    | exact superpose eq503 eq8
    | exact resolve eq8 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq605 : x = y ∨ x = y := by
    first
    | (have i₁ := eq566
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq566
    | exact resolve eq566 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq606 : x = y := by grind
  clear eq605
  have eq673 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq606
       grind)
    | exact superpose eq606 eq14
    | exact resolve eq14 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq674 : False := by grind
  exact eq674

/-- `x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
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
  have eq52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq31 X0 X1
       grind)
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq10
    | (have j1 := eq31 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X0)
       have r₂ := eq31 X0 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X1)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq10 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq268 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq63 x y
       grind)
    | exact superpose eq63 eq14
    | (have j1 := eq63 x y
       grind)
    | exact resolve eq14 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq284 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq268
    | (have j0 := eq268 X0 X1
       grind)
    | exact resolve eq268 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq268
  have eq316 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq284 X0 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq284
    | exact resolve eq284 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq492 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq274
       have i₂ := eq316 x y
       grind)
    | exact superpose eq316 eq274
    | (have j1 := eq316 (σ x) (σ y)
       grind)
    | (have r₁ := eq274
       have r₂ := eq316 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq274
       have r₂ := eq316 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq274 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq316
  have eq495 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq492
  have eq558 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq495
       grind)
    | exact superpose eq495 eq8
    | exact resolve eq8 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq597 : x = y ∨ x = y := by
    first
    | (have i₁ := eq558
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq558
    | exact resolve eq558 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq598 : x = y := by grind
  clear eq597
  have eq665 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq598
       grind)
    | exact superpose eq598 eq14
    | exact resolve eq14 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq666 : False := by grind
  exact eq666
